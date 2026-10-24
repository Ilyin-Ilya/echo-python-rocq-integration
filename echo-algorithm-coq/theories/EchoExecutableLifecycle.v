(** * Direct process lifecycle invariants for executable Echo *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableTopology.

Section EchoExecutableLifecycle.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Hypothesis initiator_in_nodes : In initiator all_nodes.
Hypothesis adj_symmetric :
  forall left right,
    config_adjacent config left right = true ->
    config_adjacent config right left = true.

Definition echo_process_lifecycle_valid
    (owner : node) (process : @echo_process node) : Prop :=
  (owner = initiator -> process_parent process = None) /\
  (owner <> initiator ->
    process_finished process = true ->
    exists parent, process_parent process = Some parent).

Definition echo_lifecycle_well_formed
    (state : @executable_echo_state node) : Prop :=
  forall owner,
    In owner all_nodes ->
    echo_process_lifecycle_valid owner (processes state owner).

Lemma initial_process_lifecycle_valid (owner : node) :
  echo_process_lifecycle_valid owner initial_echo_process.
Proof.
  unfold echo_process_lifecycle_valid, initial_echo_process.
  cbn. split.
  - intros _. reflexivity.
  - intros _ Hfinished. discriminate.
Qed.

Lemma update_process_preserves_lifecycle
    (roles : node -> @echo_process node)
    (target : node) (new_process : @echo_process node) :
  (forall owner,
      In owner all_nodes ->
      echo_process_lifecycle_valid owner (roles owner)) ->
  In target all_nodes ->
  echo_process_lifecycle_valid target new_process ->
  forall owner,
    In owner all_nodes ->
    echo_process_lifecycle_valid owner
      (update_process node_eq roles target new_process owner).
Proof.
  intros Hold Htarget Hnew owner Howner.
  unfold update_process.
  destruct (node_eq target owner) as [Heq | Hdifferent].
  - now subst owner.
  - now apply Hold.
Qed.

Lemma apply_echo_delivery_preserves_lifecycle
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_lifecycle_well_formed state ->
  In (message_receiver selected) all_nodes ->
  echo_process_lifecycle_valid
    (message_receiver selected) new_process ->
  echo_lifecycle_well_formed
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hreceiver Hnew owner Howner.
  cbn [apply_echo_delivery].
  now apply update_process_preserves_lifecycle.
Qed.

Lemma echo_initial_on_lifecycle
    (state : @executable_echo_state node) :
  echo_initial_on config state ->
  echo_lifecycle_well_formed state.
Proof.
  intros [Hstarted [Hprocesses [Hstore Hnext]]] owner Howner.
  rewrite (Hprocesses owner Howner).
  apply initial_process_lifecycle_valid.
Qed.

Lemma initiator_root_lifecycle_valid
    (pending : list node) (finished : bool) :
  echo_process_lifecycle_valid initiator
    (mkEchoProcess None pending finished).
Proof.
  unfold echo_process_lifecycle_valid. cbn. split.
  - intros _. reflexivity.
  - intros Hdifferent. contradiction.
Qed.

Lemma parented_process_lifecycle_valid
    (owner parent : node) (pending : list node) (finished : bool) :
  owner <> initiator ->
  echo_process_lifecycle_valid owner
    (mkEchoProcess (Some parent) pending finished).
Proof.
  intro Hdifferent.
  unfold echo_process_lifecycle_valid. cbn. split.
  - intro Heq. contradiction.
  - intros _. exists parent. reflexivity.
Qed.

Lemma delivery_receiver_configured
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_topology_well_formed config state ->
  EchoStep state event successor ->
  is_delivery_event event ->
  In (message_receiver (@event_message node config event)) all_nodes.
Proof.
  intros [Hparents Hqueued] Hstep Hdelivery.
  pose proof (@EchoStep_delivery_message_queued node node_eq config
    state successor event Hstep Hdelivery) as Hselected.
  now destruct (Hqueued _ Hselected) as [_ [Hreceiver _]].
Qed.

Theorem EchoStep_start_lifecycle
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  pose proof (echo_initial_on_lifecycle state Hinitial) as Hbefore.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros owner Howner. cbn [apply_echo_start].
  apply update_process_preserves_lifecycle.
  - exact Hbefore.
  - exact initiator_in_nodes.
  - apply initiator_root_lifecycle_valid.
  - exact Howner.
Qed.

Theorem EchoStep_first_request_nonleaf_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hdifferent.
  cbn [guard_holds eval_node_expr event_message] in Hdifferent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - now apply parented_process_lifecycle_valid.
Qed.

Theorem EchoStep_first_request_leaf_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoFirstRequestLeaf message) Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as Hdifferent.
  cbn [guard_holds eval_node_expr event_message] in Hdifferent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestLeaf message) first_echo_leaf_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_leaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - now apply parented_process_lifecycle_valid.
Qed.

Theorem EchoStep_repeated_request_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoRepeatedRequest message) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoRepeatedRequest message) Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoRepeatedRequest message) repeated_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action repeated_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - now apply Hlifecycle.
Qed.

Theorem EchoStep_initiator_request_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoInitiatorRequest message) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoInitiatorRequest message) Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message) initiator_echo_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorRequest message) initiator_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - rewrite Hequal. now apply Hlifecycle.
Qed.

Theorem EchoStep_participant_reply_more_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoParticipantReplyMore message parent)
    Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hdifferent.
  cbn [guard_holds eval_node_expr event_message] in Hdifferent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - now apply parented_process_lifecycle_valid.
Qed.

Theorem EchoStep_participant_reply_final_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoParticipantReplyFinal message parent)
    Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hdifferent.
  cbn [guard_holds eval_node_expr event_message] in Hdifferent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - now apply parented_process_lifecycle_valid.
Qed.

Theorem EchoStep_initiator_reply_more_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoInitiatorReplyMore message) Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyMore message) initiator_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - rewrite Hequal. apply initiator_root_lifecycle_valid.
Qed.

Theorem EchoStep_initiator_reply_final_lifecycle
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep.
  pose proof (delivery_receiver_configured state successor
    (EchoInitiatorReplyFinal message) Htopology Hstep I) as Hreceiver.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_lifecycle.
  - exact Hlifecycle.
  - exact Hreceiver.
  - rewrite Hequal. apply initiator_root_lifecycle_valid.
Qed.

Theorem EchoStep_preserves_lifecycle
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_topology_well_formed config state ->
  echo_lifecycle_well_formed state ->
  EchoStep state event successor ->
  echo_lifecycle_well_formed successor.
Proof.
  intros Htopology Hlifecycle Hstep. destruct event.
  - exact (EchoStep_start_lifecycle state successor ordered_neighbors Hstep).
  - eapply EchoStep_first_request_nonleaf_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_first_request_leaf_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_repeated_request_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_initiator_request_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_participant_reply_more_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_participant_reply_final_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_initiator_reply_more_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
  - eapply EchoStep_initiator_reply_final_lifecycle;
      [exact Htopology | exact Hlifecycle | exact Hstep].
Qed.

Lemma initial_executable_echo_state_lifecycle :
  echo_lifecycle_well_formed initial_executable_echo_state.
Proof.
  intros owner Howner.
  apply initial_process_lifecycle_valid.
Qed.

Theorem echo_reachable_lifecycle
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  echo_lifecycle_well_formed state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_lifecycle.
  - eapply EchoStep_preserves_lifecycle.
    + exact (@echo_reachable_topology node node_eq config
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

Theorem echo_reachable_initiator_parent_none
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  process_parent (processes state initiator) = None.
Proof.
  intro Hreachable.
  pose proof (echo_reachable_lifecycle state Hreachable) as Hlifecycle.
  destruct (Hlifecycle initiator initiator_in_nodes) as [Hinitiator _].
  now apply Hinitiator.
Qed.

Theorem echo_reachable_finished_participant_has_parent
    (state : @executable_echo_state node) (owner : node) :
  @echo_reachable node node_eq config state ->
  In owner all_nodes ->
  owner <> initiator ->
  process_finished (processes state owner) = true ->
  exists parent, process_parent (processes state owner) = Some parent.
Proof.
  intros Hreachable Howner Hdifferent Hfinished.
  pose proof (echo_reachable_lifecycle state Hreachable) as Hlifecycle.
  destruct (Hlifecycle owner Howner) as [_ Hparticipant].
  now apply Hparticipant.
Qed.

End EchoExecutableLifecycle.

Arguments echo_process_lifecycle_valid {node} config _ _.
Arguments echo_lifecycle_well_formed {node} config _.
