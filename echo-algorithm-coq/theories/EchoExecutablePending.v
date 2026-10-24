(** * Direct pending-list invariants for executable Echo *)

From Stdlib Require Import List Bool Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability.

Section EchoExecutablePending.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Hypothesis nodes_nodup : NoDup all_nodes.

(** A pending list is a set-like list of configured neighbors of its owner. *)
Definition echo_pending_valid (owner : node) (pending : list node) : Prop :=
  NoDup pending /\
  forall neighbor,
    In neighbor pending ->
    In neighbor all_nodes /\ adj owner neighbor = true.

Definition echo_process_pending_valid
    (owner : node) (process : @echo_process node) : Prop :=
  echo_pending_valid owner (process_pending process).

Definition echo_pending_well_formed
    (state : @executable_echo_state node) : Prop :=
  forall owner,
    In owner all_nodes ->
    echo_process_pending_valid owner (processes state owner).

Lemma echo_pending_valid_empty (owner : node) :
  echo_pending_valid owner [].
Proof.
  split; [constructor | intros neighbor Hin; contradiction].
Qed.

Lemma echo_pending_valid_neighbors (owner : node) :
  echo_pending_valid owner (nbrs all_nodes adj owner).
Proof.
  unfold echo_pending_valid, nbrs. split.
  - now apply NoDup_filter.
  - intros neighbor Hin. now apply filter_In in Hin.
Qed.

Lemma in_remove_echo_node
    (target : node) (items : list node) (candidate : node) :
  In candidate (remove_echo_node node_eq target items) ->
  In candidate items.
Proof.
  induction items as [| head tail IH]; cbn; intro Hin.
  - contradiction.
  - destruct (node_eq target head) as [Heq | Hdifferent].
    + now right.
    + destruct Hin as [Heq | Hin].
      * now left.
      * right. now apply IH.
Qed.

Lemma NoDup_remove_echo_node (target : node) (items : list node) :
  NoDup items ->
  NoDup (remove_echo_node node_eq target items).
Proof.
  induction items as [| head tail IH]; intro Hnodup; cbn.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Htail]; subst.
    destruct (node_eq target head) as [Heq | Hdifferent].
    + exact Htail.
    + constructor.
      * intro Hin. apply Hnotin.
        now apply (in_remove_echo_node target tail head).
      * now apply IH.
Qed.

Lemma echo_pending_valid_remove
    (owner target : node) (items : list node) :
  echo_pending_valid owner items ->
  echo_pending_valid owner (remove_echo_node node_eq target items).
Proof.
  intros [Hnodup Hneighbors]. split.
  - now apply NoDup_remove_echo_node.
  - intros neighbor Hin.
    apply Hneighbors.
    now apply (in_remove_echo_node target items neighbor).
Qed.

Lemma echo_pending_valid_permutation
    (owner : node) (left right : list node) :
  Permutation left right ->
  echo_pending_valid owner right ->
  echo_pending_valid owner left.
Proof.
  intros Hpermutation [Hnodup Hneighbors]. split.
  - eapply Permutation_NoDup.
    + symmetry. exact Hpermutation.
    + exact Hnodup.
  - intros neighbor Hin. apply Hneighbors.
    eapply Permutation_in; eauto.
Qed.

Lemma initial_process_pending_valid (owner : node) :
  echo_process_pending_valid owner initial_echo_process.
Proof.
  apply echo_pending_valid_empty.
Qed.

Lemma update_process_preserves_pending
    (roles : node -> @echo_process node)
    (target : node) (new_process : @echo_process node) :
  (forall owner,
      In owner all_nodes ->
      echo_process_pending_valid owner (roles owner)) ->
  (In target all_nodes ->
    echo_process_pending_valid target new_process) ->
  forall owner,
    In owner all_nodes ->
    echo_process_pending_valid owner
      (update_process node_eq roles target new_process owner).
Proof.
  intros Hold Hnew owner Howner.
  unfold update_process.
  destruct (node_eq target owner) as [Heq | Hdifferent].
  - subst owner. now apply Hnew.
  - now apply Hold.
Qed.

Lemma apply_echo_delivery_preserves_pending
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_pending_well_formed state ->
  (In (message_receiver selected) all_nodes ->
    echo_process_pending_valid (message_receiver selected) new_process) ->
  echo_pending_well_formed
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hnew owner Howner.
  cbn [apply_echo_delivery].
  now apply update_process_preserves_pending.
Qed.

Lemma echo_initial_on_pending
    (state : @executable_echo_state node) :
  echo_initial_on config state ->
  echo_pending_well_formed state.
Proof.
  intros [Hstarted [Hprocesses [Hstore Hnext]]] owner Howner.
  rewrite (Hprocesses owner Howner).
  apply initial_process_pending_valid.
Qed.

Theorem EchoStep_start_pending
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_pending_well_formed successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  pose proof (echo_initial_on_pending state Hinitial) as Hbefore.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros owner Howner. cbn [apply_echo_start].
  apply update_process_preserves_pending.
  - exact Hbefore.
  - intros Hinitiator. cbn [echo_process_pending_valid].
    eapply echo_pending_valid_permutation.
    + exact Hpermutation.
    + apply echo_pending_valid_neighbors.
  - exact Howner.
Qed.

Theorem EchoStep_first_request_nonleaf_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardPermutation IRNodesOrdered
      (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
    Hstep eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hpermutation.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_message
    event_ordered_nodes] in Hpermutation.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intros Hreceiver. cbn [echo_process_pending_valid].
    eapply echo_pending_valid_permutation.
    + exact Hpermutation.
    + apply echo_pending_valid_remove.
      apply echo_pending_valid_neighbors.
Qed.

Theorem EchoStep_first_request_leaf_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestLeaf message) first_echo_leaf_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_leaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intros Hreceiver. cbn [echo_process_pending_valid].
    apply echo_pending_valid_empty.
Qed.

Theorem EchoStep_repeated_request_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoRepeatedRequest message) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoRepeatedRequest message) repeated_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action repeated_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - now intros Hreceiver; apply Hpending.
Qed.

Theorem EchoStep_initiator_request_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoInitiatorRequest message) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
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
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intro Hreceiver. rewrite Hequal in Hreceiver |- *.
    exact (Hpending initiator Hreceiver).
Qed.

Theorem EchoStep_participant_reply_more_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intro Hreceiver. cbn [echo_process_pending_valid].
    apply echo_pending_valid_remove.
    now apply Hpending.
Qed.

Theorem EchoStep_participant_reply_final_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intros Hreceiver. cbn [echo_process_pending_valid].
    apply echo_pending_valid_empty.
Qed.

Theorem EchoStep_initiator_reply_more_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
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
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intro Hreceiver. cbn [echo_process_pending_valid].
    rewrite Hequal in Hreceiver |- *.
    apply echo_pending_valid_remove.
    exact (Hpending initiator Hreceiver).
Qed.

Theorem EchoStep_initiator_reply_final_pending
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_pending_well_formed state ->
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_pending.
  - exact Hpending.
  - intros Hreceiver. cbn [echo_process_pending_valid].
    apply echo_pending_valid_empty.
Qed.

(** Reply-specific equations expose the exact pending-list update performed
    by the canonical interpreter.  Both the "more" and "final" branches
    remove the replying sender; a final branch is selected exactly when the
    resulting list is empty. *)
Theorem EchoStep_participant_reply_more_removes_sender
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  process_pending (processes successor (message_receiver message)) =
  remove_echo_node node_eq (message_sender message)
    (process_pending (processes state (message_receiver message))).
Proof.
  intro Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  unfold apply_echo_delivery. cbn. unfold update_process.
  destruct (node_eq (message_receiver message) (message_receiver message));
    [reflexivity | contradiction].
Qed.

Theorem EchoStep_participant_reply_final_removes_sender
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  process_pending (processes successor (message_receiver message)) =
  remove_echo_node node_eq (message_sender message)
    (process_pending (processes state (message_receiver message))).
Proof.
  intro Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
    Hstep eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hempty.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  unfold apply_echo_delivery. cbn. unfold update_process.
  destruct (node_eq (message_receiver message) (message_receiver message));
    [symmetry; exact Hempty | contradiction].
Qed.

Theorem EchoStep_initiator_reply_more_removes_sender
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  process_pending (processes successor initiator) =
  remove_echo_node node_eq (message_sender message)
    (process_pending (processes state initiator)).
Proof.
  intro Hstep.
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
  unfold apply_echo_delivery. cbn. unfold update_process.
  rewrite Hequal.
  destruct (node_eq initiator initiator); [reflexivity | contradiction].
Qed.

Theorem EchoStep_initiator_reply_final_removes_sender
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  process_pending (processes successor initiator) =
  remove_echo_node node_eq (message_sender message)
    (process_pending (processes state initiator)).
Proof.
  intro Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
    Hstep eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hempty.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  unfold apply_echo_delivery. cbn. unfold update_process.
  rewrite Hequal.
  destruct (node_eq initiator initiator);
    [symmetry; exact Hempty | contradiction].
Qed.

Theorem EchoStep_preserves_pending
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_pending_well_formed state ->
  EchoStep state event successor ->
  echo_pending_well_formed successor.
Proof.
  intros Hpending Hstep. destruct event.
  - exact (EchoStep_start_pending state successor ordered_neighbors Hstep).
  - eapply EchoStep_first_request_nonleaf_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_first_request_leaf_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_repeated_request_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_initiator_request_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_participant_reply_more_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_participant_reply_final_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_initiator_reply_more_pending;
      [exact Hpending | exact Hstep].
  - eapply EchoStep_initiator_reply_final_pending;
      [exact Hpending | exact Hstep].
Qed.

Lemma initial_executable_echo_state_pending :
  echo_pending_well_formed initial_executable_echo_state.
Proof.
  intros owner Howner.
  apply initial_process_pending_valid.
Qed.

Theorem echo_reachable_pending
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  echo_pending_well_formed state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_pending.
  - eapply EchoStep_preserves_pending.
    + exact IH.
    + exact Hstep.
Qed.

Theorem echo_reachable_pending_nodup
    (state : @executable_echo_state node) (owner : node) :
  @echo_reachable node node_eq config state ->
  In owner all_nodes ->
  NoDup (process_pending (processes state owner)).
Proof.
  intros Hreachable Howner.
  destruct (echo_reachable_pending state Hreachable owner Howner)
    as [Hnodup Hneighbors].
  exact Hnodup.
Qed.

Theorem echo_reachable_pending_neighbor
    (state : @executable_echo_state node) (owner neighbor : node) :
  @echo_reachable node node_eq config state ->
  In owner all_nodes ->
  In neighbor (process_pending (processes state owner)) ->
  In neighbor all_nodes /\ adj owner neighbor = true.
Proof.
  intros Hreachable Howner Hneighbor.
  destruct (echo_reachable_pending state Hreachable owner Howner)
    as [Hnodup Hneighbors].
  now apply Hneighbors.
Qed.

End EchoExecutablePending.

Arguments echo_pending_valid {node} config _ _.
Arguments echo_process_pending_valid {node} config _ _.
Arguments echo_pending_well_formed {node} config _.
