(** * Direct post-decision safety for executable Echo

    These theorems are about the canonical [EchoStep] relation itself.  Once
    the initiator is finished, no initiator-labelled delivery rule can run,
    no successful delivery may target the initiator, and later successful
    steps preserve the initiator's finished flag. *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableCompletion
  EchoExecutableObligations.

Section EchoExecutablePostDecision.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation EchoStep := (@EchoStep node node_eq config).

(** These are precisely the three delivery tags whose canonical guards say
    that the selected receiver is the initiator. *)
Definition is_initiator_delivery_event
    (event : @echo_event node) : Prop :=
  match event with
  | EchoInitiatorRequest _ => True
  | EchoInitiatorReplyMore _ => True
  | EchoInitiatorReplyFinal _ => True
  | _ => False
  end.

(** A successful delivery updates only the selected receiver's process.  The
    lemma exposes that common interpreter effect without duplicating any
    protocol branch or validity predicate. *)
Lemma EchoStep_delivery_process_effect
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  EchoStep state event successor ->
  is_delivery_event event ->
  exists new_process : @echo_process node,
    processes successor =
      update_process node_eq (processes state)
        (message_receiver (@event_message node config event))
        new_process.
Proof.
  intros Hstep Hdelivery.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  destruct event; cbn [is_delivery_event] in Hdelivery;
    try contradiction.
  all: cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule;
    inversion Hrule; subst rule; clear Hrule Hguards.
  all: cbn [eval_action first_echo_nonleaf_rule first_echo_leaf_rule
    repeated_echo_rule initiator_echo_rule participant_ack_more_rule
    participant_ack_final_rule initiator_ack_more_rule
    initiator_ack_final_rule ir_rule_action eval_nodes_expr
    eval_process_expr eval_parent_expr eval_outbound_expr] in Haction.
  all: subst successor.
  all: eexists; reflexivity.
Qed.

(** The finished guard is part of the canonical rule table.  It therefore
    blocks every initiator-specific request or reply branch after decision. *)
Theorem EchoStep_finished_initiator_rejects_initiator_event
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  process_finished (processes state initiator) = true ->
  EchoStep state event successor ->
  is_initiator_delivery_event event ->
  False.
Proof.
  intros Hfinished Hstep Hinitiator_event.
  destruct event as
      [ordered_neighbors
      | message ordered_forwards
      | message
      | message
      | message
      | message parent
      | message parent
      | message
      | message];
    cbn [is_initiator_delivery_event] in Hinitiator_event;
    try contradiction.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardFinished IRInitiatorNode false)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr] in Hunfinished. congruence.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardFinished IRInitiatorNode false)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr] in Hunfinished. congruence.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardFinished IRInitiatorNode false)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr] in Hunfinished. congruence.
Qed.

(** More generally, after the initiator is finished, every successful
    delivery must target a different process.  Participant rules prove this
    with their receiver-not-initiator guard; initiator rules are impossible by
    the preceding theorem. *)
Theorem EchoStep_finished_initiator_not_delivery_target
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  process_finished (processes state initiator) = true ->
  EchoStep state event successor ->
  is_delivery_event event ->
  message_receiver (@event_message node config event) <> initiator.
Proof.
  intros Hfinished Hstep Hdelivery.
  destruct event as
      [ordered_neighbors
      | message ordered_forwards
      | message
      | message
      | message
      | message parent
      | message parent
      | message
      | message];
    cbn [is_delivery_event] in Hdelivery;
    try contradiction.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hnot_equal.
    exact Hnot_equal.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hnot_equal.
    exact Hnot_equal.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoRepeatedRequest message) repeated_echo_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [repeated_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hnot_equal.
    exact Hnot_equal.
  - exfalso. eapply EchoStep_finished_initiator_rejects_initiator_event.
    + exact Hfinished.
    + exact Hstep.
    + exact I.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hnot_equal.
    exact Hnot_equal.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hnot_equal.
    exact Hnot_equal.
  - exfalso. eapply EchoStep_finished_initiator_rejects_initiator_event.
    + exact Hfinished.
    + exact Hstep.
    + exact I.
  - exfalso. eapply EchoStep_finished_initiator_rejects_initiator_event.
    + exact Hfinished.
    + exact Hstep.
    + exact I.
Qed.

(** Decision is stable: startup cannot run from a finished configured
    initiator, and every later delivery updates a non-initiator process. *)
Theorem EchoStep_initiator_finished_preserved
    (initiator_in_nodes : In initiator all_nodes)
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  process_finished (processes state initiator) = true ->
  EchoStep state event successor ->
  process_finished (processes successor initiator) = true.
Proof.
  intros Hfinished Hstep.
  destruct event as
      [ordered_neighbors
      | message ordered_forwards
      | message
      | message
      | message
      | message parent
      | message parent
      | message
      | message].
  all: try (
    pose proof (EchoStep_finished_initiator_not_delivery_target
      state successor _ Hfinished Hstep I) as Hnot_target;
    destruct (EchoStep_delivery_process_effect
      state successor _ Hstep I) as [new_process Hprocesses];
    rewrite Hprocesses; cbn [event_message]; unfold update_process;
    destruct (node_eq (message_receiver message) initiator)
      as [Hequal | Hdifferent];
    [contradiction | exact Hfinished]).
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hneighbors].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  specialize (Hprocesses initiator initiator_in_nodes).
  rewrite Hprocesses in Hfinished. discriminate.
Qed.

(** The one-step result is packaged with canonical reachability so runner
    proofs can extend a decided execution without reopening branch details. *)
Corollary echo_reachable_finished_initiator_step
    (initiator_in_nodes : In initiator all_nodes)
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_reachable node_eq config state ->
  process_finished (processes state initiator) = true ->
  EchoStep state event successor ->
  echo_reachable node_eq config successor /\
  process_finished (processes successor initiator) = true.
Proof.
  intros Hreachable Hfinished Hstep. split.
  - eapply EchoReachStep; eauto.
  - eapply EchoStep_initiator_finished_preserved; eauto.
Qed.

(** The transition-level decision barrier is also a queue barrier.  Every
    queued request or reply would, by the direct obligation proofs, propagate
    a nonempty pending slot to the initiator; completion says a finished
    initiator has no such slot. *)
Theorem echo_reachable_finished_initiator_store_empty
    (nodes_nodup : NoDup all_nodes)
    (initiator_in_nodes : In initiator all_nodes)
    (adj_symmetric :
      forall left right,
        config_adjacent config left right = true ->
        config_adjacent config right left = true)
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  process_finished (processes state initiator) = true ->
  message_store state = [].
Proof.
  intros Hreachable Hfinished.
  destruct (message_store state) as [|message rest] eqn:Hstore.
  - reflexivity.
  - exfalso.
    assert (Hmessage : In message (message_store state)).
    { rewrite Hstore. now left. }
    destruct (@echo_reachable_queued_message_initiator_pending
      node node_eq config nodes_nodup initiator_in_nodes adj_symmetric
      state message Hreachable Hmessage) as [root_item Hpending].
    pose proof (@echo_reachable_finished_pending_empty
      node node_eq config state initiator Hreachable
      initiator_in_nodes Hfinished) as Hempty.
    rewrite Hempty in Hpending. contradiction.
Qed.

End EchoExecutablePostDecision.

Arguments is_initiator_delivery_event {node} _.
