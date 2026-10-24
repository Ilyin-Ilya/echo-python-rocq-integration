(** * Direct completion invariants for executable Echo *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableTopology EchoExecutableLifecycle.

Section EchoExecutableCompletion.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation EchoStep := (@EchoStep node node_eq config).

(** [finished = true] has one concrete meaning in the executable state: the
    process has received every reply it was waiting for. *)
Definition echo_process_completion_valid
    (process : @echo_process node) : Prop :=
  process_finished process = true -> process_pending process = [].

Definition echo_completion_well_formed
    (state : @executable_echo_state node) : Prop :=
  forall owner,
    In owner all_nodes ->
    echo_process_completion_valid (processes state owner).

Lemma initial_process_completion_valid :
  echo_process_completion_valid (@initial_echo_process node).
Proof.
  unfold echo_process_completion_valid, initial_echo_process.
  cbn. discriminate.
Qed.

Lemma unfinished_process_completion_valid
    (parent : option node) (pending : list node) :
  echo_process_completion_valid (mkEchoProcess parent pending false).
Proof.
  unfold echo_process_completion_valid. cbn. discriminate.
Qed.

Lemma finished_process_completion_valid (parent : option node) :
  echo_process_completion_valid (mkEchoProcess parent [] true).
Proof.
  unfold echo_process_completion_valid. cbn. reflexivity.
Qed.

Lemma update_process_preserves_completion
    (roles : node -> @echo_process node)
    (target : node) (new_process : @echo_process node) :
  (forall owner,
      In owner all_nodes ->
      echo_process_completion_valid (roles owner)) ->
  (In target all_nodes ->
    echo_process_completion_valid new_process) ->
  forall owner,
    In owner all_nodes ->
    echo_process_completion_valid
      (update_process node_eq roles target new_process owner).
Proof.
  intros Hold Hnew owner Howner.
  unfold update_process.
  destruct (node_eq target owner) as [Heq | Hdifferent].
  - subst owner. now apply Hnew.
  - now apply Hold.
Qed.

Lemma apply_echo_delivery_preserves_completion
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_completion_well_formed state ->
  (In (message_receiver selected) all_nodes ->
    echo_process_completion_valid new_process) ->
  echo_completion_well_formed
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hnew owner Howner.
  cbn [apply_echo_delivery].
  now apply update_process_preserves_completion.
Qed.

Lemma echo_initial_on_completion
    (state : @executable_echo_state node) :
  echo_initial_on config state ->
  echo_completion_well_formed state.
Proof.
  intros [Hstarted [Hprocesses [Hstore Hnext]]] owner Howner.
  rewrite (Hprocesses owner Howner).
  apply initial_process_completion_valid.
Qed.

Theorem EchoStep_start_completion
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_completion_well_formed successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  pose proof (echo_initial_on_completion state Hinitial) as Hbefore.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros owner Howner. cbn [apply_echo_start].
  apply update_process_preserves_completion.
  - exact Hbefore.
  - intros Hinitiator. apply unfinished_process_completion_valid.
  - exact Howner.
Qed.

Theorem EchoStep_first_request_nonleaf_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intros Hreceiver. apply unfinished_process_completion_valid.
Qed.

Theorem EchoStep_first_request_leaf_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestLeaf message) first_echo_leaf_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_leaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intros Hreceiver. apply finished_process_completion_valid.
Qed.

Theorem EchoStep_repeated_request_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoRepeatedRequest message) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoRepeatedRequest message) repeated_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action repeated_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - now intros Hreceiver; apply Hcompletion.
Qed.

Theorem EchoStep_initiator_request_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoInitiatorRequest message) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
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
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intro Hreceiver. rewrite Hequal in Hreceiver.
    exact (Hcompletion initiator Hreceiver).
Qed.

Theorem EchoStep_participant_reply_more_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intros Hreceiver. apply unfinished_process_completion_valid.
Qed.

Theorem EchoStep_participant_reply_final_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intros Hreceiver. apply finished_process_completion_valid.
Qed.

Theorem EchoStep_initiator_reply_more_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyMore message) initiator_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intros Hreceiver. apply unfinished_process_completion_valid.
Qed.

Theorem EchoStep_initiator_reply_final_completion
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_completion_well_formed state ->
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_completion.
  - exact Hcompletion.
  - intros Hreceiver. apply finished_process_completion_valid.
Qed.

Theorem EchoStep_preserves_completion
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_completion_well_formed state ->
  EchoStep state event successor ->
  echo_completion_well_formed successor.
Proof.
  intros Hcompletion Hstep. destruct event.
  - exact (EchoStep_start_completion state successor ordered_neighbors Hstep).
  - eapply EchoStep_first_request_nonleaf_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_first_request_leaf_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_repeated_request_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_initiator_request_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_participant_reply_more_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_participant_reply_final_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_initiator_reply_more_completion;
      [exact Hcompletion | exact Hstep].
  - eapply EchoStep_initiator_reply_final_completion;
      [exact Hcompletion | exact Hstep].
Qed.

Lemma initial_executable_echo_state_completion :
  echo_completion_well_formed initial_executable_echo_state.
Proof.
  intros owner Howner.
  apply initial_process_completion_valid.
Qed.

Theorem echo_reachable_completion
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  echo_completion_well_formed state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_completion.
  - eapply EchoStep_preserves_completion.
    + exact IH.
    + exact Hstep.
Qed.

Theorem echo_reachable_finished_pending_empty
    (state : @executable_echo_state node) (owner : node) :
  @echo_reachable node node_eq config state ->
  In owner all_nodes ->
  process_finished (processes state owner) = true ->
  process_pending (processes state owner) = [].
Proof.
  intros Hreachable Howner Hfinished.
  apply (echo_reachable_completion state Hreachable owner Howner).
  exact Hfinished.
Qed.

End EchoExecutableCompletion.

Section FinishedParticipantCompletion.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).

Hypothesis initiator_in_nodes : In initiator all_nodes.
Hypothesis adj_symmetric :
  forall left right,
    config_adjacent config left right = true ->
    config_adjacent config right left = true.

(** A finished participant is fully settled locally: it has a parent and no
    remaining child replies to collect. *)
Theorem echo_reachable_finished_participant_complete
    (state : @executable_echo_state node) (owner : node) :
  @echo_reachable node node_eq config state ->
  In owner all_nodes ->
  owner <> initiator ->
  process_finished (processes state owner) = true ->
  exists parent,
    process_parent (processes state owner) = Some parent /\
    process_pending (processes state owner) = [].
Proof.
  intros Hreachable Howner Hdifferent Hfinished.
  destruct (@echo_reachable_finished_participant_has_parent
    node node_eq config initiator_in_nodes adj_symmetric state owner
    Hreachable Howner Hdifferent Hfinished) as [parent Hparent].
  exists parent. split.
  - exact Hparent.
  - exact (@echo_reachable_finished_pending_empty
      node node_eq config state owner Hreachable Howner Hfinished).
Qed.

End FinishedParticipantCompletion.

Arguments echo_process_completion_valid {node} _.
Arguments echo_completion_well_formed {node} config _.
