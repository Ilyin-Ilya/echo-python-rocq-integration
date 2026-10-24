(** * Direct discovery/parent invariant for executable Echo

    A non-initiator becomes discovered only when its first request installs a
    parent.  This small invariant is the structural link needed by the later
    request-obligation proof: every discovered participant can be followed one
    step toward the initiator. *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableForest.

Section EchoExecutableDiscovery.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Definition echo_discovered_participants_parented
    (state : @executable_echo_state node) : Prop :=
  forall owner,
    In owner all_nodes ->
    owner <> initiator ->
    echo_discovered state owner ->
    exists parent,
      process_parent (processes state owner) = Some parent.

Lemma apply_echo_delivery_preserves_discovered_participants_parented
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_discovered_participants_parented state ->
  (In (message_receiver selected) all_nodes ->
   message_receiver selected <> initiator ->
   new_process <> initial_echo_process ->
   exists parent, process_parent new_process = Some parent) ->
  echo_discovered_participants_parented
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hparented Hnew owner Howner Hnot_initiator Hdiscovered.
  unfold echo_discovered in Hdiscovered.
  destruct (node_eq (message_receiver selected) owner)
      as [Hequal | Hdifferent].
  - subst owner.
    rewrite apply_echo_delivery_process_self in Hdiscovered.
    rewrite apply_echo_delivery_process_self.
    now apply Hnew.
  - rewrite apply_echo_delivery_process_other in Hdiscovered
      by exact Hdifferent.
    rewrite apply_echo_delivery_process_other by exact Hdifferent.
    apply Hparented; try assumption.
Qed.

Theorem EchoStep_start_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros owner Howner Hnot_initiator Hdiscovered.
  unfold echo_discovered in Hdiscovered.
  assert (Hinitiator_not_owner : initiator <> owner) by congruence.
  rewrite apply_echo_start_process_other in Hdiscovered
    by exact Hinitiator_not_owner.
  rewrite (Hprocesses owner Howner) in Hdiscovered.
  contradiction.
Qed.

Theorem EchoStep_first_request_nonleaf_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    exists (message_sender message). reflexivity.
Qed.

Theorem EchoStep_first_request_leaf_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestLeaf message) first_echo_leaf_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_leaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    exists (message_sender message). reflexivity.
Qed.

Theorem EchoStep_repeated_request_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoRepeatedRequest message) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoRepeatedRequest message) repeated_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action repeated_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    now apply Hparented.
Qed.

Theorem EchoStep_initiator_request_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoInitiatorRequest message) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
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
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    contradiction.
Qed.

Theorem EchoStep_participant_reply_more_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    exists parent. reflexivity.
Qed.

Theorem EchoStep_participant_reply_final_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    exists parent. reflexivity.
Qed.

Theorem EchoStep_initiator_reply_more_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
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
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    contradiction.
Qed.

Theorem EchoStep_initiator_reply_final_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_discovered_participants_parented state ->
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
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
  apply apply_echo_delivery_preserves_discovered_participants_parented.
  - exact Hparented.
  - intros Hreceiver Hnot_initiator Hdiscovered.
    contradiction.
Qed.

Theorem EchoStep_preserves_discovered_participants_parented
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_discovered_participants_parented state ->
  EchoStep state event successor ->
  echo_discovered_participants_parented successor.
Proof.
  intros Hparented Hstep. destruct event.
  - now apply EchoStep_start_discovered_participants_parented in Hstep.
  - eapply EchoStep_first_request_nonleaf_discovered_participants_parented;
      eauto.
  - eapply EchoStep_first_request_leaf_discovered_participants_parented;
      eauto.
  - eapply EchoStep_repeated_request_discovered_participants_parented; eauto.
  - eapply EchoStep_initiator_request_discovered_participants_parented; eauto.
  - eapply EchoStep_participant_reply_more_discovered_participants_parented;
      eauto.
  - eapply EchoStep_participant_reply_final_discovered_participants_parented;
      eauto.
  - eapply EchoStep_initiator_reply_more_discovered_participants_parented;
      eauto.
  - eapply EchoStep_initiator_reply_final_discovered_participants_parented;
      eauto.
Qed.

Lemma initial_executable_echo_state_discovered_participants_parented :
  echo_discovered_participants_parented initial_executable_echo_state.
Proof.
  intros owner Howner Hnot_initiator Hdiscovered.
  exfalso. apply Hdiscovered. reflexivity.
Qed.

Theorem echo_reachable_discovered_participants_parented
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_discovered_participants_parented state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_discovered_participants_parented.
  - eapply EchoStep_preserves_discovered_participants_parented; eauto.
Qed.

End EchoExecutableDiscovery.

Arguments echo_discovered_participants_parented {node} config _.
