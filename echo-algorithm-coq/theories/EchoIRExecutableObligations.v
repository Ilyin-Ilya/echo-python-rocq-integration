(** Direct obligation invariants for the executable generic Echo IR. *)
From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery
  EchoIRExecutableTopology EchoIRExecutableRequestAccounting
  EchoIRExecutableRequestParent EchoIRExecutableReplyDiscovery
  EchoIRExecutableRequestReply.

Section EchoIRExecutableObligations.
Variable node : Type.
Variable node_eq : forall left right : node, {left = right} + {left <> right}.

Definition echo_ir_bool_value_contents (value : ir_value node IRBool) : bool :=
  match value with IRBoolValue result => result end.

Lemma echo_ir_bool_value_eta (value : ir_value node IRBool) :
  value = IRBoolValue (echo_ir_bool_value_contents value).
Proof.
  exact
    (match value as selected in ir_value _ kind return
      match kind as actual return ir_value node actual -> Prop with
      | IRBool => fun selected =>
          selected = IRBoolValue (echo_ir_bool_value_contents selected)
      | _ => fun _ => True
      end selected
    with
    | IRBoolValue item => eq_refl
    | IRNatValue _ => I
    | IRNodeValue _ => I
    | IROptionNodeValue _ => I
    | IRListNodeValue _ => I
    | IRMessageRefValue _ => I
    end).
Qed.

Definition echo_ir_reply_noninitiator_senders_discovered
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    ir_message_sender message <> echo_ir_config_initiator node config ->
    echo_ir_local_discovered node state (ir_message_sender message).

Definition echo_ir_parent_replies_from_finished
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    echo_ir_parent_value node state (ir_message_sender message) =
      Some (ir_message_receiver message) ->
    echo_ir_finished_value node state (ir_message_sender message) = true.

Definition echo_ir_reply_edges_unique
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall first second,
    In first (ir_message_store state) ->
    In second (ir_message_store state) ->
    ir_message_kind first = EchoIRReply ->
    ir_message_kind second = EchoIRReply ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.

Lemma echo_ir_remove_preserves_reply_edges_unique state selected_id :
  echo_ir_reply_edges_unique state ->
  echo_ir_reply_edges_unique (ir_remove_selected_message state selected_id).
Proof.
  intros unique first second first_in second_in
    first_kind second_kind same_sender same_receiver.
  apply unique; try assumption;
    cbn [ir_remove_selected_message ir_message_store] in *.
  - now apply (echo_ir_remove_message_in node selected_id _ first).
  - now apply (echo_ir_remove_message_in node selected_id _ second).
Qed.

Lemma echo_ir_emit_preserves_reply_edges_unique
    state kind sender receivers payload :
  echo_ir_reply_edges_unique state ->
  NoDup receivers ->
  (kind = EchoIRReply ->
    forall old receiver,
      In old (ir_message_store state) ->
      ir_message_kind old = EchoIRReply ->
      In receiver receivers ->
      ir_message_sender old = sender ->
      ir_message_receiver old = receiver ->
      False) ->
  echo_ir_reply_edges_unique
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros unique receivers_nodup fresh first second first_in second_in
    first_kind second_kind same_sender same_receiver.
  cbn [ir_emit_messages ir_message_store] in first_in, second_in.
  apply in_app_or in first_in as [first_old | first_new];
    apply in_app_or in second_in as [second_old | second_new].
  - now eapply unique.
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) kind sender receivers payload
      second second_new) as [second_sender second_receiver].
    assert (kind_reply : kind = EchoIRReply).
    { rewrite <- second_kind. symmetry.
      now apply (echo_ir_materialized_message_kind node
        (ir_next_message_id state) kind sender receivers payload second). }
    exfalso. exact (fresh kind_reply first (ir_message_receiver second)
      first_old first_kind second_receiver
      ltac:(now rewrite same_sender, second_sender) same_receiver).
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) kind sender receivers payload
      first first_new) as [first_sender first_receiver].
    assert (kind_reply : kind = EchoIRReply).
    { rewrite <- first_kind. symmetry.
      now apply (echo_ir_materialized_message_kind node
        (ir_next_message_id state) kind sender receivers payload first). }
    exfalso. exact (fresh kind_reply second (ir_message_receiver first)
      second_old second_kind first_receiver
      ltac:(now rewrite <- same_sender, first_sender)
      ltac:(now symmetry)).
  - eapply echo_ir_materialized_receivers_injective; eauto.
Qed.

Lemma echo_ir_emit_nonreply_preserves_reply_edges_unique
    state kind sender receivers payload :
  echo_ir_reply_edges_unique state ->
  kind <> EchoIRReply ->
  echo_ir_reply_edges_unique
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros unique not_reply first second first_in second_in
    first_kind second_kind same_sender same_receiver.
  cbn [ir_emit_messages ir_message_store] in first_in, second_in.
  apply in_app_or in first_in as [first_old | first_new];
    apply in_app_or in second_in as [second_old | second_new].
  - now eapply unique.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload
      second second_new) as emitted_kind.
    rewrite second_kind in emitted_kind.
    exfalso. apply not_reply. now symmetry.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload
      first first_new) as emitted_kind.
    rewrite first_kind in emitted_kind.
    exfalso. apply not_reply. now symmetry.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload
      first first_new) as emitted_kind.
    rewrite first_kind in emitted_kind.
    exfalso. apply not_reply. now symmetry.
Qed.

Lemma echo_ir_start_reply_edges_unique config state successor certificates :
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros empty action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  intros first second first_in second_in first_kind.
  cbn [ir_emit_messages ir_message_store] in first_in.
  apply in_app_or in first_in as [old | emitted].
  - change (In first (ir_message_store state)) in old.
    rewrite empty in old. contradiction.
  - pose proof (echo_ir_materialized_message_kind node
      _ EchoIRRequest _ _ [] first emitted) as emitted_kind.
    rewrite first_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_initial_reply_edges_unique :
  echo_ir_reply_edges_unique (@echo_initial_state node).
Proof. intros first second first_in. contradiction. Qed.

Lemma echo_ir_update_preserves_reply_edges_unique
    state owner parent pending finished :
  echo_ir_reply_edges_unique state ->
  echo_ir_reply_edges_unique
    (echo_ir_update_process node node_eq state owner parent pending finished).
Proof. exact (fun unique => unique). Qed.

Lemma echo_ir_response_preserves_reply_edges_unique state selected :
  echo_ir_reply_edges_unique state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRRequest ->
  echo_ir_reply_edges_unique
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id selected))
      EchoIRReply (ir_message_receiver selected)
      [ir_message_sender selected] []).
Proof.
  intros unique reverse selected_in request_kind.
  apply echo_ir_emit_preserves_reply_edges_unique.
  - now apply echo_ir_remove_preserves_reply_edges_unique.
  - repeat constructor; simpl; congruence.
  - intros _ old receiver old_in old_kind [same | impossible]
      same_sender same_receiver; [subst receiver | contradiction].
    cbn [ir_remove_selected_message ir_message_store] in old_in.
    exfalso. eapply reverse.
    + exact selected_in.
    + now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ old).
    + exact request_kind.
    + exact old_kind.
    + now symmetry.
    + now symmetry.
Qed.

Lemma echo_ir_parent_response_preserves_reply_edges_unique
    state (selected : ir_message node echo_ir_signature) (parent : node) :
  echo_ir_reply_edges_unique state ->
  echo_ir_parent_replies_from_finished state ->
  echo_ir_parent_value node state (ir_message_receiver selected) = Some parent ->
  echo_ir_finished_value node state (ir_message_receiver selected) = false ->
  echo_ir_reply_edges_unique
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id selected))
      EchoIRReply (ir_message_receiver selected) [parent] []).
Proof.
  intros unique parent_replies installed unfinished.
  apply echo_ir_emit_preserves_reply_edges_unique.
  - now apply echo_ir_remove_preserves_reply_edges_unique.
  - repeat constructor; simpl; congruence.
  - intros _ old receiver old_in old_kind [same | impossible]
      same_sender same_receiver; [subst receiver | contradiction].
    cbn [ir_remove_selected_message ir_message_store] in old_in.
    pose proof (parent_replies old
      (echo_ir_remove_message_in node (ir_message_id selected) _ old old_in)
      old_kind) as old_finished.
    assert (old_parent : echo_ir_parent_value node state
      (ir_message_sender old) = Some (ir_message_receiver old)).
    { now rewrite same_sender, same_receiver. }
    specialize (old_finished old_parent).
    rewrite same_sender, unfinished in old_finished. discriminate.
Qed.

Lemma echo_ir_update_preserves_parent_replies_from_finished
    state owner parent pending finished :
  echo_ir_parent_replies_from_finished state ->
  (forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    ir_message_sender message = owner ->
    ir_option_node_value_contents parent = Some (ir_message_receiver message) ->
    finished = true) ->
  echo_ir_parent_replies_from_finished
    (echo_ir_update_process node node_eq state owner parent pending finished).
Proof.
  intros invariant updated message queued kind parent_link.
  destruct (node_eq owner (ir_message_sender message)) as [same | different].
  - subst owner.
    assert (new_finished : finished = true).
    { apply updated with (message := message); try assumption.
      - reflexivity.
      - unfold echo_ir_parent_value, echo_ir_update_process in parent_link.
        rewrite ir_set_local_field_read_different in parent_link
          by discriminate.
        rewrite ir_set_local_field_read_different in parent_link
          by discriminate.
        rewrite ir_set_local_field_same in parent_link.
        rewrite (ir_option_node_value_eta parent) in parent_link.
        exact parent_link. }
    unfold echo_ir_finished_value, echo_ir_update_process.
    rewrite ir_set_local_field_same. exact new_finished.
  - unfold echo_ir_parent_value, echo_ir_update_process in parent_link.
    repeat rewrite ir_set_local_field_read_other_process in parent_link
      by exact different.
    unfold echo_ir_finished_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    now apply invariant with (message := message).
Qed.

Lemma echo_ir_remove_preserves_parent_replies_from_finished state selected_id :
  echo_ir_parent_replies_from_finished state ->
  echo_ir_parent_replies_from_finished
    (ir_remove_selected_message state selected_id).
Proof.
  intros invariant message queued kind parent_link.
  apply invariant with (message := message); try assumption.
  cbn [ir_remove_selected_message ir_message_store] in queued.
  now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_emit_preserves_parent_replies_from_finished
    state kind sender receivers payload :
  echo_ir_parent_replies_from_finished state ->
  (kind = EchoIRReply -> forall receiver,
    In receiver receivers ->
    echo_ir_parent_value node state sender = Some receiver ->
    echo_ir_finished_value node state sender = true) ->
  echo_ir_parent_replies_from_finished
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros invariant emitted message queued message_kind parent_link.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | new].
  - now apply invariant with (message := message).
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) kind sender receivers payload message new)
      as [same_sender receiver_in].
    rewrite same_sender in parent_link |- *.
    apply emitted with (receiver := ir_message_receiver message).
    + rewrite <- message_kind. symmetry.
      now apply (echo_ir_materialized_message_kind node
        (ir_next_message_id state) kind sender receivers payload message).
    + exact receiver_in.
    + exact parent_link.
Qed.

Lemma echo_ir_start_parent_replies_from_finished
    config state successor certificates :
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros empty action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  intros message queued reply_kind parent_link.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - change (In message (ir_message_store state)) in old.
    rewrite empty in old. contradiction.
  - pose proof (echo_ir_materialized_message_kind node
      _ EchoIRRequest _ _ [] message emitted) as emitted_kind.
    rewrite reply_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_initial_parent_replies_from_finished :
  echo_ir_parent_replies_from_finished (@echo_initial_state node).
Proof. intros message queued. contradiction. Qed.

Lemma echo_ir_nonleaf_parent_replies_from_finished
    config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  ~ echo_ir_local_discovered node state (ir_message_receiver message) ->
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros sender_discovery receiver_not_root receiver_initial invariant action.
  unfold echo_ir_reply_noninitiator_senders_discovered in sender_discovery.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_replies_from_finished.
  - apply echo_ir_remove_preserves_parent_replies_from_finished.
    apply echo_ir_update_preserves_parent_replies_from_finished.
    + exact invariant.
    + intros old queued reply_kind same_sender parent_link.
      exfalso. apply receiver_initial.
      rewrite <- same_sender.
      apply sender_discovery with (message := old); try assumption.
      now rewrite same_sender.
  - discriminate.
Qed.

Lemma echo_ir_leaf_parent_replies_from_finished
    config state successor message certificates :
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  set (updated := echo_ir_update_process node node_eq state
    (ir_message_receiver message)
    (IROptionNodeValue (Some (ir_message_sender message)))
    (IRListNodeValue []) true).
  apply echo_ir_emit_preserves_parent_replies_from_finished.
  - apply echo_ir_remove_preserves_parent_replies_from_finished.
    unfold updated. apply echo_ir_update_preserves_parent_replies_from_finished.
    + exact invariant.
    + intros. reflexivity.
  - intros _ receiver receiver_in parent_link.
    change (echo_ir_finished_value node updated
      (ir_message_receiver message) = true).
    unfold updated, echo_ir_finished_value, echo_ir_update_process.
    rewrite ir_set_local_field_same. reflexivity.
Qed.

Lemma echo_ir_repeated_parent_replies_from_finished
    config state successor message certificates :
  echo_ir_request_parent_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros request_parent queued request_kind invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_replies_from_finished.
  - now apply echo_ir_remove_preserves_parent_replies_from_finished.
  - intros _ receiver [same | impossible] parent_link;
      [subst receiver | contradiction].
    change (echo_ir_parent_value node state (ir_message_receiver message) =
      Some (ir_message_sender message)) in parent_link.
    exfalso. now apply (request_parent message queued request_kind).
Qed.

Lemma echo_ir_root_request_parent_replies_from_finished
    config state successor message certificates :
  echo_ir_initiator_parent_none node config state ->
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros root_parent invariant action.
  unfold echo_ir_initiator_parent_none in root_parent.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_replies_from_finished.
  - now apply echo_ir_remove_preserves_parent_replies_from_finished.
  - intros _ receiver [same | impossible] parent_link;
      [subst receiver | contradiction].
    change (echo_ir_parent_value node state
      (echo_ir_config_initiator node config) =
      Some (ir_message_sender message)) in parent_link.
    unfold echo_ir_parent_value in parent_link.
    rewrite root_parent in parent_link. discriminate.
Qed.

Lemma echo_ir_participant_more_parent_replies_from_finished
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_value node state (ir_message_receiver message) = false ->
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros unfinished invariant action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    apply echo_ir_remove_preserves_parent_replies_from_finished.
    apply echo_ir_update_preserves_parent_replies_from_finished.
    + exact invariant.
    + intros old queued reply_kind same_sender new_parent.
      exfalso.
      pose proof (invariant old queued reply_kind) as old_finished.
      assert (old_link : echo_ir_parent_value node state
        (ir_message_sender old) = Some (ir_message_receiver old)).
      { rewrite same_sender.
        unfold echo_ir_parent_value. rewrite parent_value.
        cbn in new_parent. now injection new_parent as <-. }
      specialize (old_finished old_link).
      rewrite same_sender, unfinished in old_finished. discriminate.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_parent_replies_from_finished
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    set (updated := echo_ir_update_process node node_eq state
      (ir_message_receiver message) (IROptionNodeValue (Some parent_node))
      (IRListNodeValue []) true).
    change (echo_ir_parent_replies_from_finished
      (ir_emit_messages
        (ir_remove_selected_message updated (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_parent_replies_from_finished.
    + apply echo_ir_remove_preserves_parent_replies_from_finished.
      unfold updated. apply echo_ir_update_preserves_parent_replies_from_finished.
      * exact invariant.
      * intros. reflexivity.
    + intros _ receiver receiver_in parent_link.
      change (echo_ir_finished_value node updated
        (ir_message_receiver message) = true).
      unfold updated, echo_ir_finished_value, echo_ir_update_process.
      rewrite ir_set_local_field_same. reflexivity.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_parent_replies_from_finished
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_parent_replies_from_finished.
  apply echo_ir_update_preserves_parent_replies_from_finished.
  - exact invariant.
  - intros old queued reply_kind same_sender impossible. discriminate.
Qed.

Lemma echo_ir_initiator_final_parent_replies_from_finished
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_replies_from_finished state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_parent_replies_from_finished.
  apply echo_ir_update_preserves_parent_replies_from_finished.
  - exact invariant.
  - intros. reflexivity.
Qed.

Lemma echo_ir_nonleaf_reply_edges_unique
    config state successor message certificates :
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros unique action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_nonreply_preserves_reply_edges_unique.
  - now apply echo_ir_remove_preserves_reply_edges_unique.
  - discriminate.
Qed.

Lemma echo_ir_leaf_reply_edges_unique
    config state successor message certificates :
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros reverse queued request_kind unique action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_response_preserves_reply_edges_unique; assumption.
Qed.

Lemma echo_ir_repeated_reply_edges_unique
    config state successor message certificates :
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros reverse queued request_kind unique action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_response_preserves_reply_edges_unique; assumption.
Qed.

Lemma echo_ir_root_request_reply_edges_unique
    config state successor message certificates :
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros reverse queued request_kind receiver_root unique action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  unfold echo_ir_config_initiator in receiver_root.
  rewrite <- receiver_root.
  apply echo_ir_response_preserves_reply_edges_unique; assumption.
Qed.

Lemma echo_ir_participant_more_reply_edges_unique
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros unique action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    now apply echo_ir_remove_preserves_reply_edges_unique.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_reply_edges_unique
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_replies_from_finished state ->
  echo_ir_finished_value node state (ir_message_receiver message) = false ->
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros parent_replies unfinished unique action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    apply (echo_ir_parent_response_preserves_reply_edges_unique state message
      parent_node).
    + exact unique.
    + exact parent_replies.
    + unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
    + exact unfinished.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_reply_edges_unique
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros unique action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  now apply echo_ir_remove_preserves_reply_edges_unique.
Qed.

Lemma echo_ir_initiator_final_reply_edges_unique
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_edges_unique state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros unique action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  now apply echo_ir_remove_preserves_reply_edges_unique.
Qed.

Lemma echo_ir_enabled_receiver_unfinished
    config state message certificates rule :
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    rule = IRRuleEnabled ->
  In (echo_ir_equal node
      (echo_ir_finished node (echo_ir_receiver node))
      (echo_ir_bool node false))
    (ir_rule_guards rule) ->
  echo_ir_finished_value node state (ir_message_receiver message) = false.
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_equal node
      (echo_ir_finished node (echo_ir_receiver node))
      (echo_ir_bool node false)) enabled member) as guard.
  unfold echo_ir_equal, echo_ir_finished, echo_ir_receiver,
    echo_ir_bool in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (echo_ir_bool_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRFinished))
    in guard.
  destruct (echo_ir_bool_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRFinished))
    eqn:finished; cbn in guard; try discriminate.
  unfold echo_ir_finished_value.
  rewrite (echo_ir_bool_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRFinished)).
  now rewrite finished.
Qed.

Theorem EchoStep_preserves_parent_replies_from_finished
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_initiator_parent_none node config state ->
  echo_ir_discovered_participants_parented node config state ->
  echo_ir_request_parent_distinct node state ->
  echo_ir_reply_noninitiator_senders_discovered config state ->
  echo_ir_parent_replies_from_finished state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_parent_replies_from_finished successor.
Proof.
  intros root_parent discovered_parented request_parent
    sender_discovery invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_parent_replies_from_finished.
    + now apply (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
        message certificates (@echo_ir_first_request_nonleaf_rule node)
        enabled ltac:(cbn [echo_ir_first_request_nonleaf_rule]; now left))
        as receiver_not_root.
      pose proof (echo_ir_first_nonleaf_enabled_parent_none node node_eq
        config state message certificates enabled) as receiver_parent_none.
      assert (receiver_initial :
        ~ echo_ir_local_discovered node state (ir_message_receiver message)).
      { intro receiver_discovered.
        destruct (discovered_parented (ir_message_receiver message)
          receiver_not_root receiver_discovered) as [parent installed].
        rewrite receiver_parent_none in installed. discriminate. }
      eapply echo_ir_nonleaf_parent_replies_from_finished; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        now apply echo_ir_leaf_parent_replies_from_finished with
          (config := config) (state := state) (message := message)
          (certificates := certificates).
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           pose proof (echo_ir_resolved_delivery_queued node state
             external_event message certificates resolved) as queued.
           pose proof (echo_ir_enabled_request_pattern_kind node node_eq
             config state message certificates
             (@echo_ir_repeated_request_rule node) eq_refl enabled)
             as request_kind.
           eapply echo_ir_repeated_parent_replies_from_finished; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              now apply echo_ir_root_request_parent_replies_from_finished with
                (config := config) (state := state) (message := message)
                (certificates := certificates).
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 pose proof (echo_ir_enabled_expected_parent node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)) as old_parent.
                 pose proof (echo_ir_enabled_receiver_unfinished config state
                   message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     repeat (first [left; reflexivity | right])))
                   as unfinished.
                 eapply echo_ir_participant_more_parent_replies_from_finished;
                   eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     now apply
                       echo_ir_participant_final_parent_replies_from_finished
                       with (config := config) (state := state)
                       (message := message) (certificates := certificates).
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq config
                           state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         now apply
                           echo_ir_initiator_more_parent_replies_from_finished
                           with (config := config) (state := state)
                           (message := message) (certificates := certificates).
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             now apply
                               echo_ir_initiator_final_parent_replies_from_finished
                               with (config := config) (state := state)
                               (message := message)
                               (certificates := certificates).
                         *** contradiction.
Qed.

Theorem EchoStep_preserves_reply_edges_unique
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct node state ->
  echo_ir_parent_replies_from_finished state ->
  echo_ir_reply_edges_unique state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_reply_edges_unique successor.
Proof.
  intros reverse parent_replies unique step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_reply_edges_unique.
    + now apply (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      eapply echo_ir_nonleaf_reply_edges_unique; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_resolved_delivery_queued node state
          external_event message certificates resolved) as queued.
        pose proof (echo_ir_enabled_request_pattern_kind node node_eq
          config state message certificates
          (@echo_ir_first_request_leaf_rule node) eq_refl enabled)
          as request_kind.
        eapply echo_ir_leaf_reply_edges_unique; eauto.
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           pose proof (echo_ir_resolved_delivery_queued node state
             external_event message certificates resolved) as queued.
           pose proof (echo_ir_enabled_request_pattern_kind node node_eq
             config state message certificates
             (@echo_ir_repeated_request_rule node) eq_refl enabled)
             as request_kind.
           eapply echo_ir_repeated_reply_edges_unique; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              pose proof (echo_ir_resolved_delivery_queued node state
                external_event message certificates resolved) as queued.
              pose proof (echo_ir_enabled_request_pattern_kind node node_eq
                config state message certificates
                (@echo_ir_initiator_request_rule node) eq_refl enabled)
                as request_kind.
              pose proof (echo_ir_enabled_initiator_receiver node node_eq
                config state message certificates
                (@echo_ir_initiator_request_rule node) enabled
                ltac:(cbn [echo_ir_initiator_request_rule]; now left))
                as receiver_root.
              eapply echo_ir_root_request_reply_edges_unique; eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 eapply echo_ir_participant_more_reply_edges_unique; eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     pose proof (echo_ir_enabled_expected_parent node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)) as installed.
                     pose proof (echo_ir_enabled_receiver_unfinished config
                       state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         repeat (first [left; reflexivity | right])))
                       as unfinished.
                     eapply echo_ir_participant_final_reply_edges_unique;
                       eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         eapply echo_ir_initiator_more_reply_edges_unique;
                           eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             eapply echo_ir_initiator_final_reply_edges_unique;
                               eauto.
                         *** contradiction.
Qed.

Lemma echo_ir_remove_preserves_reply_sender_discovery config state selected_id :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  echo_ir_reply_noninitiator_senders_discovered config
    (ir_remove_selected_message state selected_id).
Proof.
  intros invariant message queued kind nonroot.
  apply invariant with (message := message); try assumption.
  cbn [ir_remove_selected_message ir_message_store] in queued.
  now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_update_preserves_reply_sender_discovery
    config state owner parent pending finished :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  (owner = echo_ir_config_initiator node config \/
   echo_ir_local_discovered node
     (echo_ir_update_process node node_eq state owner parent pending finished)
     owner) ->
  echo_ir_reply_noninitiator_senders_discovered config
    (echo_ir_update_process node node_eq state owner parent pending finished).
Proof.
  intros invariant [root | owner_discovered] message queued kind nonroot.
  - apply echo_ir_update_process_other_discovery.
    + intro same. apply nonroot. now rewrite <- root, same.
    + now apply invariant with (message := message).
  - apply (echo_ir_update_process_discovery_monotone node node_eq
      state owner parent pending finished owner_discovered).
    now apply invariant with (message := message).
Qed.

Lemma echo_ir_emit_preserves_reply_sender_discovery
    config state kind sender receivers payload :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  (kind = EchoIRReply ->
   sender <> echo_ir_config_initiator node config ->
   echo_ir_local_discovered node state sender) ->
  echo_ir_reply_noninitiator_senders_discovered config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros invariant new_sender message queued message_kind nonroot.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - now apply invariant with (message := message).
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) kind sender receivers payload message emitted)
      as [same_sender receiver_in].
    rewrite same_sender in nonroot |- *.
    apply new_sender; [|exact nonroot].
    rewrite <- message_kind. symmetry.
    now apply (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload message).
Qed.

Lemma echo_ir_seen_guard_discovered config state message certificates :
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    (@echo_ir_repeated_request_rule node) = IRRuleEnabled ->
  echo_ir_local_discovered node state (ir_message_receiver message).
Proof.
  intro enabled.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) (@echo_ir_repeated_request_rule node)
    (echo_ir_process_seen node (echo_ir_receiver node)) enabled
    ltac:(cbn [echo_ir_repeated_request_rule]; now right; left)) as seen.
  unfold echo_ir_process_seen, echo_ir_parent, echo_ir_finished,
    echo_ir_receiver in seen.
  cbn [eval_ir_expr ir_event_message] in seen.
  rewrite (ir_option_node_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRParent))
    in seen.
  rewrite (echo_ir_bool_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRFinished))
    in seen.
  destruct (ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent))
    as [installed |] eqn:parent_contents;
    destruct (echo_ir_bool_value_contents
      (ir_processes state (ir_message_receiver message) EchoIRFinished))
      eqn:finished_contents;
    cbn in seen; try discriminate.
  - left. unfold echo_ir_parent_value.
    rewrite (ir_option_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRParent)).
    rewrite parent_contents. cbn. intro impossible. inversion impossible.
  - left. unfold echo_ir_parent_value.
    rewrite (ir_option_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRParent)).
    rewrite parent_contents. cbn. intro impossible. inversion impossible.
  - right. right. unfold echo_ir_finished_value.
    rewrite (echo_ir_bool_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRFinished)).
    rewrite finished_contents. cbn. intro impossible. inversion impossible.
Qed.

Lemma echo_ir_start_reply_sender_discovery config state successor certificates :
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros empty action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  intros message queued reply_kind nonroot.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - change (In message (ir_message_store state)) in old.
    rewrite empty in old. contradiction.
  - pose proof (echo_ir_materialized_message_kind node
      _ EchoIRRequest _ _ [] message emitted) as emitted_kind.
    rewrite reply_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_nonleaf_reply_sender_discovery config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_reply_sender_discovery.
  - apply echo_ir_remove_preserves_reply_sender_discovery.
    apply echo_ir_update_preserves_reply_sender_discovery; [exact invariant |].
    right. apply echo_ir_update_process_some_owner_discovered.
  - discriminate.
Qed.

Lemma echo_ir_leaf_reply_sender_discovery config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  set (updated := echo_ir_update_process node node_eq state
    (ir_message_receiver message)
    (IROptionNodeValue (Some (ir_message_sender message)))
    (IRListNodeValue []) true).
  apply echo_ir_emit_preserves_reply_sender_discovery.
  - apply echo_ir_remove_preserves_reply_sender_discovery.
    unfold updated. apply echo_ir_update_preserves_reply_sender_discovery;
      [exact invariant |].
    right. apply echo_ir_update_process_finished_owner_discovered.
  - intros _ nonroot. unfold ir_remove_selected_message, updated.
    apply echo_ir_update_process_finished_owner_discovered.
Qed.

Lemma echo_ir_repeated_reply_sender_discovery config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  echo_ir_local_discovered node state (ir_message_receiver message) ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant discovered action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_reply_sender_discovery.
  - now apply echo_ir_remove_preserves_reply_sender_discovery.
  - intros _ nonroot. unfold ir_remove_selected_message. exact discovered.
Qed.

Lemma echo_ir_root_request_reply_sender_discovery config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_reply_sender_discovery.
  - now apply echo_ir_remove_preserves_reply_sender_discovery.
  - intros _ impossible. contradiction.
Qed.

Lemma echo_ir_participant_more_reply_sender_discovery
    config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    apply echo_ir_remove_preserves_reply_sender_discovery.
    apply echo_ir_update_preserves_reply_sender_discovery; [exact invariant |].
    right. apply echo_ir_update_process_some_owner_discovered.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_reply_sender_discovery
    config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    set (updated := echo_ir_update_process node node_eq state
      (ir_message_receiver message) (IROptionNodeValue (Some parent_node))
      (IRListNodeValue []) true).
    change (echo_ir_reply_noninitiator_senders_discovered config
      (ir_emit_messages
        (ir_remove_selected_message updated (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_reply_sender_discovery.
    + apply echo_ir_remove_preserves_reply_sender_discovery.
      unfold updated. apply echo_ir_update_preserves_reply_sender_discovery;
        [exact invariant |].
      right. apply echo_ir_update_process_finished_owner_discovered.
    + intros _ nonroot. unfold ir_remove_selected_message, updated.
      apply echo_ir_update_process_finished_owner_discovered.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_reply_sender_discovery
    config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending))
    in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_reply_sender_discovery.
  apply echo_ir_update_preserves_reply_sender_discovery; [exact invariant |].
  now left.
Qed.

Lemma echo_ir_initiator_final_reply_sender_discovery
    config state successor message certificates :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_reply_sender_discovery.
  apply echo_ir_update_preserves_reply_sender_discovery; [exact invariant |].
  now left.
Qed.

Theorem EchoStep_preserves_reply_noninitiator_senders_discovered
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_reply_noninitiator_senders_discovered config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_reply_noninitiator_senders_discovered config successor.
Proof.
  intros invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_reply_sender_discovery.
    + now apply (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      now apply echo_ir_nonleaf_reply_sender_discovery with
        (config := config) (state := state) (message := message)
        (certificates := certificates).
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        now apply echo_ir_leaf_reply_sender_discovery with
          (config := config) (state := state) (message := message)
          (certificates := certificates).
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_repeated_reply_sender_discovery.
           ++ exact invariant.
           ++ now apply (echo_ir_seen_guard_discovered config state
                message certificates).
           ++ exact action.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              now apply echo_ir_root_request_reply_sender_discovery with
                (config := config) (state := state) (message := message)
                (certificates := certificates).
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 now apply echo_ir_participant_more_reply_sender_discovery with
                   (config := config) (state := state) (message := message)
                   (certificates := certificates).
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     now apply
                       echo_ir_participant_final_reply_sender_discovery with
                       (config := config) (state := state) (message := message)
                       (certificates := certificates).
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq config
                           state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         now apply
                           echo_ir_initiator_more_reply_sender_discovery with
                           (config := config) (state := state)
                           (message := message) (certificates := certificates).
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             now apply
                               echo_ir_initiator_final_reply_sender_discovery
                               with (config := config) (state := state)
                               (message := message)
                               (certificates := certificates).
                         *** contradiction.
Qed.

Lemma echo_ir_initial_reply_noninitiator_senders_discovered config :
  echo_ir_reply_noninitiator_senders_discovered config
    (@echo_initial_state node).
Proof. intros message queued. contradiction. Qed.

Theorem echo_ir_path_preserves_reply_noninitiator_senders_discovered
    config initial final :
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_reply_noninitiator_senders_discovered config initial ->
  echo_ir_reply_noninitiator_senders_discovered config final.
Proof.
  intros reachable. induction reachable; intro invariant.
  - exact invariant.
  - apply IHreachable.
    eapply EchoStep_preserves_reply_noninitiator_senders_discovered.
    + exact invariant.
    + exists rule. exact H.
Qed.

Theorem echo_reachable_reply_noninitiator_senders_discovered config state :
  echo_reachable node node_eq config state ->
  echo_ir_reply_noninitiator_senders_discovered config state.
Proof.
  intro reachable.
  eapply echo_ir_path_preserves_reply_noninitiator_senders_discovered.
  - exact reachable.
  - apply echo_ir_initial_reply_noninitiator_senders_discovered.
Qed.

Definition echo_ir_parent_reply_bundle config state : Prop :=
  echo_ir_request_reply_bundle node config state /\
  echo_ir_initiator_parent_none node config state /\
  echo_ir_reply_noninitiator_senders_discovered config state /\
  echo_ir_parent_replies_from_finished state.

Lemma EchoStep_preserves_parent_reply_bundle config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_parent_reply_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_parent_reply_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric
    [request_bundle [root_parent [sender_discovery parent_replies]]] step.
  destruct request_bundle as
    [topology [discovered [accounting [reply_support reverse]]]].
  assert (request_bundle_after :
    echo_ir_request_reply_bundle node config successor).
  { eapply EchoStep_preserves_request_reply_bundle.
    - exact initiator_in.
    - exact neighbors_valid.
    - exact symmetric.
    - exact (conj topology
        (conj discovered
          (conj accounting (conj reply_support reverse)))).
    - exact step. }
  assert (root_after :
    echo_ir_initiator_parent_none node config successor).
  { eapply EchoStep_preserves_initiator_parent_none; eauto. }
  assert (sender_after :
    echo_ir_reply_noninitiator_senders_discovered config successor).
  { eapply EchoStep_preserves_reply_noninitiator_senders_discovered; eauto. }
  assert (parent_replies_after :
    echo_ir_parent_replies_from_finished successor).
  { eapply EchoStep_preserves_parent_replies_from_finished.
    - exact root_parent.
    - exact discovered.
    - exact (proj2 (proj2 (proj2 accounting))).
    - exact sender_discovery.
    - exact parent_replies.
    - exact step. }
  exact (conj request_bundle_after
    (conj root_after (conj sender_after parent_replies_after))).
Qed.

Lemma echo_ir_initial_parent_reply_bundle config :
  echo_ir_parent_reply_bundle config (@echo_initial_state node).
Proof.
  split; [apply echo_ir_initial_request_reply_bundle |].
  split; [apply echo_ir_initial_initiator_parent_none |].
  split.
  - apply echo_ir_initial_reply_noninitiator_senders_discovered.
  - apply echo_ir_initial_parent_replies_from_finished.
Qed.

Theorem echo_ir_path_preserves_parent_reply_bundle config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_parent_reply_bundle config initial ->
  echo_ir_parent_reply_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_parent_reply_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_parent_replies_from_finished config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_parent_replies_from_finished state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_parent_reply_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_parent_reply_bundle config)) as bundle.
  exact (proj2 (proj2 (proj2 bundle))).
Qed.

Definition echo_ir_reply_edge_bundle config state : Prop :=
  echo_ir_parent_reply_bundle config state /\
  echo_ir_reply_edges_unique state.

Lemma EchoStep_preserves_reply_edge_bundle config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_reply_edge_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_reply_edge_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric
    [parent_bundle unique] step.
  split.
  - eapply EchoStep_preserves_parent_reply_bundle; eauto.
  - eapply EchoStep_preserves_reply_edges_unique.
    + exact (proj2 (proj2 (proj2 (proj2 (proj1 parent_bundle))))).
    + exact (proj2 (proj2 (proj2 parent_bundle))).
    + exact unique.
    + exact step.
Qed.

Lemma echo_ir_initial_reply_edge_bundle config :
  echo_ir_reply_edge_bundle config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_parent_reply_bundle.
  - apply echo_ir_initial_reply_edges_unique.
Qed.

Theorem echo_ir_path_preserves_reply_edge_bundle config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_reply_edge_bundle config initial ->
  echo_ir_reply_edge_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_reply_edge_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_reply_edges_unique config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_reply_edges_unique state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_reply_edge_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_reply_edge_bundle config)) as bundle.
  exact (proj2 bundle).
Qed.

(** Every queued request is represented by the receiver in the sender's
    generated pending field. *)
Definition echo_ir_queued_requests_pending
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    In (ir_message_receiver message)
      (echo_ir_pending_value node state (ir_message_sender message)).

Lemma echo_ir_remove_node_preserves_other
    (selected candidate : node) (items : list node) :
  candidate <> selected ->
  In candidate items ->
  In candidate (ir_remove_node node_eq selected items).
Proof.
  intros different member. induction items as [|head rest IH]; cbn in *.
  - contradiction.
  - destruct (node_eq selected head) as [same | not_same].
    + subst head. destruct member as [same | member].
      * exfalso. apply different. now symmetry.
      * exact member.
    + destruct member as [same | member].
      * now left.
      * right. now apply IH.
Qed.

Lemma echo_ir_remove_preserves_queued_requests_pending state selected_id :
  echo_ir_queued_requests_pending state ->
  echo_ir_queued_requests_pending
    (ir_remove_selected_message state selected_id).
Proof.
  intros invariant message queued request_kind.
  apply invariant with (message := message); try assumption.
  cbn [ir_remove_selected_message ir_message_store] in queued.
  now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_update_preserves_queued_requests_pending
    state owner parent pending finished :
  echo_ir_queued_requests_pending state ->
  (forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    ir_message_sender message = owner ->
    In (ir_message_receiver message) pending) ->
  echo_ir_queued_requests_pending
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished).
Proof.
  intros invariant updated message queued request_kind.
  destruct (node_eq owner (ir_message_sender message)) as [same | different].
  - subst owner.
    unfold echo_ir_pending_value, echo_ir_update_process.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    apply updated with (message := message); try assumption; reflexivity.
  - unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    now apply invariant with (message := message).
Qed.

Lemma echo_ir_emit_preserves_queued_requests_pending
    state kind sender receivers payload :
  echo_ir_queued_requests_pending state ->
  (kind = EchoIRRequest ->
    forall receiver,
      In receiver receivers ->
      In receiver (echo_ir_pending_value node state sender)) ->
  echo_ir_queued_requests_pending
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros invariant emitted_pending message queued request_kind.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - now apply invariant with (message := message).
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) kind sender receivers payload message emitted)
      as [same_sender receiver_in].
    pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload message emitted)
      as same_kind.
    rewrite request_kind in same_kind. subst kind.
    rewrite same_sender.
    now apply emitted_pending.
Qed.

Lemma echo_ir_emit_nonrequest_preserves_queued_requests_pending
    state kind sender receivers payload :
  echo_ir_queued_requests_pending state ->
  kind <> EchoIRRequest ->
  echo_ir_queued_requests_pending
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros invariant not_request.
  apply echo_ir_emit_preserves_queued_requests_pending.
  - exact invariant.
  - now intros request_kind.
Qed.

Lemma echo_ir_initial_queued_requests_pending :
  echo_ir_queued_requests_pending (@echo_initial_state node).
Proof. intros message queued. contradiction. Qed.

Lemma echo_ir_update_process_pending_same
    state owner parent pending finished :
  echo_ir_pending_value node
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished) owner = pending.
Proof.
  unfold echo_ir_pending_value, echo_ir_update_process.
  rewrite ir_set_local_field_read_different by discriminate.
  now rewrite ir_set_local_field_same.
Qed.

Lemma echo_ir_unparented_noninitiator_has_no_queued_requests
    config state owner :
  echo_ir_request_senders_provenanced node config state ->
  owner <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state owner = None ->
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    ir_message_sender message = owner ->
    False.
Proof.
  intros provenance nonroot no_parent message queued request_kind sender_owner.
  destruct (provenance message queued request_kind) as
    [sender_root | [parent installed]].
  - apply nonroot. now rewrite <- sender_owner.
  - rewrite sender_owner, no_parent in installed. discriminate.
Qed.

Lemma echo_ir_start_queued_requests_pending config state successor certificates :
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros empty action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  intros message queued request_kind.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - change (In message (ir_message_store state)) in old.
    rewrite empty in old. contradiction.
  - destruct (echo_ir_materialized_message_fields node _ EchoIRRequest _ _ []
      message emitted) as [same_sender receiver_in].
    rewrite same_sender.
    change (In (ir_message_receiver message)
      (echo_ir_pending_value node
        (echo_ir_update_process node node_eq state
          (echo_ir_config_initiator node config) (IROptionNodeValue None)
          (IRListNodeValue
            (ir_config_neighbors config
              (echo_ir_config_initiator node config)))
          false)
        (echo_ir_config_initiator node config))).
    rewrite echo_ir_update_process_pending_same. exact receiver_in.
Qed.

Lemma echo_ir_nonleaf_queued_requests_pending
    config state successor message certificates :
  echo_ir_request_senders_provenanced node config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  echo_ir_queued_requests_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros provenance nonroot no_parent invariant action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_queued_requests_pending.
  - apply echo_ir_remove_preserves_queued_requests_pending.
    apply echo_ir_update_preserves_queued_requests_pending.
    + exact invariant.
    + intros old queued request_kind same_sender. exfalso.
      eapply echo_ir_unparented_noninitiator_has_no_queued_requests; eauto.
  - intros _ receiver receiver_in.
    change (In receiver
      (echo_ir_pending_value node
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some (ir_message_sender message)))
          (IRListNodeValue
            (ir_remove_node node_eq (ir_message_sender message)
              (ir_config_neighbors config (ir_message_receiver message))))
          false)
        (ir_message_receiver message))).
    rewrite echo_ir_update_process_pending_same. exact receiver_in.
Qed.

Lemma echo_ir_leaf_queued_requests_pending
    config state successor message certificates :
  echo_ir_request_senders_provenanced node config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  echo_ir_queued_requests_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros provenance nonroot no_parent invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_nonrequest_preserves_queued_requests_pending.
  - apply echo_ir_remove_preserves_queued_requests_pending.
    apply echo_ir_update_preserves_queued_requests_pending.
    + exact invariant.
    + intros old queued request_kind same_sender. exfalso.
      eapply echo_ir_unparented_noninitiator_has_no_queued_requests; eauto.
  - discriminate.
Qed.

Lemma echo_ir_repeated_queued_requests_pending
    config state successor message certificates :
  echo_ir_queued_requests_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_nonrequest_preserves_queued_requests_pending.
  - now apply echo_ir_remove_preserves_queued_requests_pending.
  - discriminate.
Qed.

Lemma echo_ir_root_request_queued_requests_pending
    config state successor message certificates :
  echo_ir_queued_requests_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_nonrequest_preserves_queued_requests_pending.
  - now apply echo_ir_remove_preserves_queued_requests_pending.
  - discriminate.
Qed.

Lemma echo_ir_reply_more_update_preserves_queued_requests_pending
    state (selected : ir_message node echo_ir_signature) owner parent finished :
  echo_ir_queued_requests_pending state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  owner = ir_message_receiver selected ->
  echo_ir_queued_requests_pending
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue
        (ir_remove_node node_eq (ir_message_sender selected)
          (echo_ir_pending_value node state owner))) finished).
Proof.
  intros invariant reverse selected_in reply_kind owner_receiver.
  apply echo_ir_update_preserves_queued_requests_pending.
  - exact invariant.
  - intros request request_in request_kind request_sender.
    apply echo_ir_remove_node_preserves_other.
    + intro same_receiver.
      eapply reverse.
      * exact request_in.
      * exact selected_in.
      * exact request_kind.
      * exact reply_kind.
      * now rewrite request_sender, owner_receiver.
      * exact same_receiver.
    + pose proof (invariant request request_in request_kind) as pending.
      now rewrite request_sender in pending.
Qed.

Lemma echo_ir_reply_final_update_preserves_queued_requests_pending
    state (selected : ir_message node echo_ir_signature) owner parent finished :
  echo_ir_queued_requests_pending state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  owner = ir_message_receiver selected ->
  ir_remove_node node_eq (ir_message_sender selected)
    (echo_ir_pending_value node state owner) = [] ->
  echo_ir_queued_requests_pending
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue []) finished).
Proof.
  intros invariant reverse selected_in reply_kind owner_receiver empty.
  apply echo_ir_update_preserves_queued_requests_pending.
  - exact invariant.
  - intros request request_in request_kind request_sender.
    exfalso.
    destruct (node_eq (ir_message_receiver request)
      (ir_message_sender selected)) as [same_receiver | different].
    + eapply reverse.
      * exact request_in.
      * exact selected_in.
      * exact request_kind.
      * exact reply_kind.
      * now rewrite request_sender, owner_receiver.
      * exact same_receiver.
    + pose proof (invariant request request_in request_kind) as pending.
      rewrite request_sender in pending.
      pose proof (echo_ir_remove_node_preserves_other
        (ir_message_sender selected) (ir_message_receiver request)
        (echo_ir_pending_value node state owner) different pending) as remains.
      rewrite empty in remains. contradiction.
Qed.

Lemma echo_ir_participant_more_queued_requests_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_queued_requests_pending state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros invariant reverse queued reply_kind action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    apply echo_ir_remove_preserves_queued_requests_pending.
    apply echo_ir_reply_more_update_preserves_queued_requests_pending;
      try assumption; reflexivity.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_queued_requests_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_queued_requests_pending state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state (ir_message_receiver message)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros invariant reverse queued reply_kind empty action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    change (echo_ir_queued_requests_pending
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_nonrequest_preserves_queued_requests_pending.
    + apply echo_ir_remove_preserves_queued_requests_pending.
      apply (echo_ir_reply_final_update_preserves_queued_requests_pending
        state message (ir_message_receiver message)
        (IROptionNodeValue (Some parent_node)) true);
        try assumption; reflexivity.
    + discriminate.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_queued_requests_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_queued_requests_pending state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros invariant reverse queued reply_kind receiver_root action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_queued_requests_pending.
  apply echo_ir_reply_more_update_preserves_queued_requests_pending;
    try assumption.
  now symmetry.
Qed.

Lemma echo_ir_initiator_final_queued_requests_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_queued_requests_pending state ->
  echo_ir_request_reply_reverse_distinct node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros invariant reverse queued reply_kind receiver_root empty action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_queued_requests_pending.
  apply (echo_ir_reply_final_update_preserves_queued_requests_pending
    state message (echo_ir_config_initiator node config)
    (IROptionNodeValue None) true).
  - exact invariant.
  - exact reverse.
  - exact queued.
  - exact reply_kind.
  - now symmetry.
  - exact empty.
Qed.

Lemma echo_ir_enabled_receiver_parent_none
    config state message certificates rule :
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    rule = IRRuleEnabled ->
  In (echo_ir_equal node
      (echo_ir_parent node (echo_ir_receiver node))
      (echo_ir_option_none node))
    (ir_rule_guards rule) ->
  echo_ir_parent_value node state (ir_message_receiver message) = None.
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_equal node
      (echo_ir_parent node (echo_ir_receiver node))
      (echo_ir_option_none node)) enabled member) as guard.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_receiver,
    echo_ir_option_none in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  injection guard as equal.
  unfold echo_ir_parent_value.
  rewrite (ir_option_node_value_eta
    (ir_processes state
      (ir_message_receiver message) EchoIRParent)) in equal |- *.
  cbn in equal |- *.
  destruct (ir_option_node_value_contents
    (ir_processes state
      (ir_message_receiver message) EchoIRParent)) as [parent |].
  - discriminate.
  - reflexivity.
Qed.

Lemma echo_ir_enabled_reply_pattern_kind
    config state message certificates rule :
  ir_rule_pattern rule =
    (@IRDeliveryPattern echo_ir_signature EchoIRReply) ->
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    rule = IRRuleEnabled ->
  ir_message_kind message = EchoIRReply.
Proof.
  intros rule_pattern enabled.
  pose proof (eval_ir_rule_enabled_pattern node_eq config state
    (IRRuntimeDeliver message certificates) rule enabled) as pattern.
  rewrite rule_pattern in pattern.
  cbn [ir_event_pattern_matches] in pattern.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply (ir_message_kind message)) as [same | different].
  - now symmetry.
  - discriminate.
Qed.

Lemma echo_ir_enabled_receiver_removed_pending_empty
    config state message certificates rule :
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    rule = IRRuleEnabled ->
  In (echo_ir_is_empty node
      (echo_ir_removed_pending node (echo_ir_receiver node)))
    (ir_rule_guards rule) ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state (ir_message_receiver message)) = [].
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_is_empty node
      (echo_ir_removed_pending node (echo_ir_receiver node)))
    enabled member) as guard.
  unfold echo_ir_is_empty, echo_ir_removed_pending, echo_ir_remove,
    echo_ir_sender, echo_ir_pending, echo_ir_receiver in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (ir_list_node_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRPending)) in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  unfold echo_ir_pending_value.
  rewrite (ir_list_node_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRPending)).
  cbn.
  destruct (ir_remove_node node_eq (ir_message_sender message)
    (ir_list_node_value_contents
      (ir_processes state (ir_message_receiver message) EchoIRPending)))
    as [|first rest] eqn:remaining.
  - reflexivity.
  - discriminate.
Qed.

Lemma echo_ir_enabled_initiator_removed_pending_empty
    config state message certificates rule :
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    rule = IRRuleEnabled ->
  In (echo_ir_is_empty node
      (echo_ir_removed_pending node (echo_ir_initiator node)))
    (ir_rule_guards rule) ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)) = [].
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_is_empty node
      (echo_ir_removed_pending node (echo_ir_initiator node)))
    enabled member) as guard.
  unfold echo_ir_is_empty, echo_ir_removed_pending, echo_ir_remove,
    echo_ir_sender, echo_ir_pending, echo_ir_initiator in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  unfold echo_ir_pending_value, echo_ir_config_initiator.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)).
  cbn.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)).
  cbn.
  destruct (ir_remove_node node_eq (ir_message_sender message)
    (ir_list_node_value_contents
      (ir_processes state
        (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
        EchoIRPending))) as [|first rest] eqn:remaining.
  - reflexivity.
  - discriminate.
Qed.

Theorem EchoStep_preserves_queued_requests_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_request_senders_provenanced node config state ->
  echo_ir_request_reply_reverse_distinct node state ->
  echo_ir_queued_requests_pending state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_queued_requests_pending successor.
Proof.
  intros provenance reverse invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_queued_requests_pending.
    + now apply (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
        message certificates (@echo_ir_first_request_nonleaf_rule node)
        enabled ltac:(cbn [echo_ir_first_request_nonleaf_rule]; now left))
        as nonroot.
      pose proof (echo_ir_first_nonleaf_enabled_parent_none node node_eq
        config state message certificates enabled) as no_parent.
      eapply echo_ir_nonleaf_queued_requests_pending; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
          message certificates (@echo_ir_first_request_leaf_rule node)
          enabled ltac:(cbn [echo_ir_first_request_leaf_rule]; now left))
          as nonroot.
        pose proof (echo_ir_enabled_receiver_parent_none config state message
          certificates (@echo_ir_first_request_leaf_rule node) enabled
          ltac:(cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
            now right; left)) as no_parent.
        eapply echo_ir_leaf_queued_requests_pending; eauto.
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_repeated_queued_requests_pending; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              eapply echo_ir_root_request_queued_requests_pending; eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 pose proof (echo_ir_resolved_delivery_queued node state
                   external_event message certificates resolved) as queued.
                 pose proof (echo_ir_enabled_reply_pattern_kind config state
                   message certificates
                   (@echo_ir_participant_reply_more_rule node) eq_refl enabled)
                   as reply_kind.
                 eapply echo_ir_participant_more_queued_requests_pending;
                   eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     pose proof (echo_ir_resolved_delivery_queued node state
                       external_event message certificates resolved) as queued.
                     pose proof (echo_ir_enabled_reply_pattern_kind config state
                       message certificates
                       (@echo_ir_participant_reply_final_rule node)
                       eq_refl enabled) as reply_kind.
                     pose proof
                       (echo_ir_enabled_receiver_removed_pending_empty config
                         state message certificates
                         (@echo_ir_participant_reply_final_rule node) enabled
                         ltac:(cbn [echo_ir_participant_reply_final_rule];
                           repeat (first [left; reflexivity | right])))
                       as empty.
                     eapply echo_ir_participant_final_queued_requests_pending;
                       eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         pose proof (echo_ir_resolved_delivery_queued node state
                           external_event message certificates resolved)
                           as queued.
                         pose proof (echo_ir_enabled_reply_pattern_kind config
                           state message certificates
                           (@echo_ir_initiator_reply_more_rule node)
                           eq_refl enabled) as reply_kind.
                         pose proof (echo_ir_enabled_initiator_receiver node
                           node_eq config state message certificates
                           (@echo_ir_initiator_reply_more_rule node) enabled
                           ltac:(cbn [echo_ir_initiator_reply_more_rule];
                             now left)) as receiver_root.
                         eapply echo_ir_initiator_more_queued_requests_pending;
                           eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             pose proof (echo_ir_resolved_delivery_queued node
                               state external_event message certificates
                               resolved) as queued.
                             pose proof
                               (echo_ir_enabled_reply_pattern_kind config state
                                 message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 eq_refl enabled) as reply_kind.
                             pose proof (echo_ir_enabled_initiator_receiver node
                               node_eq config state message certificates
                               (@echo_ir_initiator_reply_final_rule node) enabled
                               ltac:(cbn [echo_ir_initiator_reply_final_rule];
                                 now left)) as receiver_root.
                             pose proof
                               (echo_ir_enabled_initiator_removed_pending_empty
                                 config state message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 enabled
                                 ltac:(cbn [echo_ir_initiator_reply_final_rule];
                                   repeat
                                     (first [left; reflexivity | right])))
                               as empty.
                             eapply
                               echo_ir_initiator_final_queued_requests_pending;
                               eauto.
                         *** contradiction.
Qed.

Definition echo_ir_request_pending_bundle config state : Prop :=
  echo_ir_reply_edge_bundle config state /\
  echo_ir_queued_requests_pending state.

Lemma EchoStep_preserves_request_pending_bundle
    config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_request_pending_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_request_pending_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric [edge_bundle pending] step.
  assert (edge_after : echo_ir_reply_edge_bundle config successor).
  { eapply EchoStep_preserves_reply_edge_bundle; eauto. }
  split; [exact edge_after |].
  destruct edge_bundle as [parent_bundle reply_unique].
  destruct parent_bundle as
    [request_bundle [root_parent [reply_discovery parent_replies]]].
  destruct request_bundle as
    [topology [discovered [accounting [reply_support reverse]]]].
  destruct accounting as [[request_unique provenance] accounting_tail].
  eapply EchoStep_preserves_queued_requests_pending; eauto.
Qed.

Lemma echo_ir_initial_request_pending_bundle config :
  echo_ir_request_pending_bundle config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_reply_edge_bundle.
  - apply echo_ir_initial_queued_requests_pending.
Qed.

Theorem echo_ir_path_preserves_request_pending_bundle config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_request_pending_bundle config initial ->
  echo_ir_request_pending_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_request_pending_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_queued_requests_pending config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_queued_requests_pending state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_request_pending_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_request_pending_bundle config)) as bundle.
  exact (proj2 bundle).
Qed.

Definition echo_ir_unfinished_children_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall child parent,
    In child (ir_config_nodes config) ->
    echo_ir_parent_value node state child = Some parent ->
    echo_ir_finished_value node state child = false ->
    In child (echo_ir_pending_value node state parent).

Lemma echo_ir_processes_preserve_unfinished_children_pending
    config left right :
  echo_ir_unfinished_children_pending config left ->
  ir_processes right = ir_processes left ->
  echo_ir_unfinished_children_pending config right.
Proof.
  intros invariant processes child parent child_in parent_link unfinished.
  unfold echo_ir_parent_value in parent_link.
  unfold echo_ir_finished_value in unfinished.
  unfold echo_ir_pending_value.
  rewrite processes in parent_link, unfinished |- *.
  now apply invariant with (child := child) (parent := parent).
Qed.

Lemma echo_ir_remove_preserves_unfinished_children_pending
    config state selected_id :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_unfinished_children_pending config
    (ir_remove_selected_message state selected_id).
Proof.
  intro invariant. eapply echo_ir_processes_preserve_unfinished_children_pending.
  - exact invariant.
  - reflexivity.
Qed.

Lemma echo_ir_emit_preserves_unfinished_children_pending
    config state kind sender receivers payload :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_unfinished_children_pending config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intro invariant. eapply echo_ir_processes_preserve_unfinished_children_pending.
  - exact invariant.
  - reflexivity.
Qed.

Lemma echo_ir_update_preserves_unfinished_children_pending
    config state owner new_parent new_pending new_finished :
  echo_ir_unfinished_children_pending config state ->
  (forall parent,
    In owner (ir_config_nodes config) ->
    new_parent = Some parent ->
    new_finished = false ->
    In owner
      (echo_ir_pending_value node
        (echo_ir_update_process node node_eq state owner
          (IROptionNodeValue new_parent) (IRListNodeValue new_pending)
          new_finished) parent)) ->
  (forall child parent,
    In child (ir_config_nodes config) ->
    child <> owner ->
    echo_ir_parent_value node state child = Some parent ->
    echo_ir_finished_value node state child = false ->
    In child
      (echo_ir_pending_value node
        (echo_ir_update_process node node_eq state owner
          (IROptionNodeValue new_parent) (IRListNodeValue new_pending)
          new_finished) parent)) ->
  echo_ir_unfinished_children_pending config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue new_parent) (IRListNodeValue new_pending)
      new_finished).
Proof.
  intros invariant owner_case other_case child parent child_in
    parent_link unfinished.
  destruct (node_eq owner child) as [same | different].
  - subst child.
    unfold echo_ir_parent_value, echo_ir_update_process in parent_link.
    rewrite ir_set_local_field_read_different in parent_link by discriminate.
    rewrite ir_set_local_field_read_different in parent_link by discriminate.
    rewrite ir_set_local_field_same in parent_link.
    unfold echo_ir_finished_value, echo_ir_update_process in unfinished.
    rewrite ir_set_local_field_same in unfinished.
    now apply owner_case with (parent := parent).
  - unfold echo_ir_parent_value, echo_ir_update_process in parent_link.
    repeat rewrite ir_set_local_field_read_other_process in parent_link
      by exact different.
    unfold echo_ir_finished_value, echo_ir_update_process in unfinished.
    repeat rewrite ir_set_local_field_read_other_process in unfinished
      by exact different.
    now apply other_case with (child := child) (parent := parent).
Qed.

Lemma echo_ir_initial_unfinished_children_pending config :
  echo_ir_unfinished_children_pending config (@echo_initial_state node).
Proof.
  intros child parent child_in parent_link. discriminate.
Qed.

Lemma echo_ir_start_unfinished_children_pending
    config state successor certificates :
  (forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_parent_value node state owner = None) ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros parents_none action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_unfinished_children_pending.
  apply echo_ir_update_preserves_unfinished_children_pending.
  - intros child parent child_in parent_link unfinished.
    rewrite (parents_none child child_in) in parent_link. discriminate.
  - intros parent owner_in parent_link. discriminate.
  - intros child parent child_in different parent_link unfinished.
    rewrite (parents_none child child_in) in parent_link. discriminate.
Qed.

Lemma echo_ir_unparented_noninitiator_has_no_children
    config state owner :
  echo_ir_parent_sources_provenanced node config state ->
  owner <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state owner = None ->
  forall child,
    echo_ir_parent_value node state child = Some owner ->
    False.
Proof.
  intros sources nonroot no_parent child child_parent.
  destruct (sources child owner child_parent) as
    [owner_root | [grandparent installed]].
  - contradiction.
  - rewrite no_parent in installed. discriminate.
Qed.

Lemma echo_ir_nonleaf_unfinished_children_pending
    config state successor message certificates :
  echo_ir_request_senders_provenanced node config state ->
  echo_ir_parent_sources_provenanced node config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_queued_requests_pending state ->
  echo_ir_unfinished_children_pending config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros senders sources nonroot no_parent queued request_kind
    requests invariant action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_unfinished_children_pending.
  apply echo_ir_remove_preserves_unfinished_children_pending.
  apply echo_ir_update_preserves_unfinished_children_pending.
  - exact invariant.
  - intros parent owner_in parent_link unfinished.
    injection parent_link as <-.
    assert (different : ir_message_receiver message <>
      ir_message_sender message).
    { intro same.
      eapply echo_ir_unparented_noninitiator_has_no_queued_requests
        with (message := message); eauto. }
    pose proof (requests message queued request_kind) as pending.
    unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    exact pending.
  - intros child parent child_in child_different child_parent child_unfinished.
    destruct (node_eq (ir_message_receiver message) parent)
      as [same_parent | parent_different].
    + subst parent. exfalso.
      eapply echo_ir_unparented_noninitiator_has_no_children; eauto.
    + pose proof (invariant child parent child_in child_parent
        child_unfinished) as pending.
      unfold echo_ir_pending_value, echo_ir_update_process.
      repeat rewrite ir_set_local_field_read_other_process
        by exact parent_different.
      exact pending.
Qed.

Lemma echo_ir_leaf_unfinished_children_pending
    config state successor message certificates :
  echo_ir_parent_sources_provenanced node config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  echo_ir_unfinished_children_pending config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros sources nonroot no_parent invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_unfinished_children_pending.
  apply echo_ir_remove_preserves_unfinished_children_pending.
  apply echo_ir_update_preserves_unfinished_children_pending.
  - exact invariant.
  - intros parent owner_in parent_link unfinished. discriminate.
  - intros child parent child_in child_different child_parent child_unfinished.
    destruct (node_eq (ir_message_receiver message) parent)
      as [same_parent | parent_different].
    + subst parent. exfalso.
      eapply echo_ir_unparented_noninitiator_has_no_children; eauto.
    + pose proof (invariant child parent child_in child_parent
        child_unfinished) as pending.
      unfold echo_ir_pending_value, echo_ir_update_process.
      repeat rewrite ir_set_local_field_read_other_process
        by exact parent_different.
      exact pending.
Qed.

Lemma echo_ir_repeated_unfinished_children_pending
    config state successor message certificates :
  echo_ir_unfinished_children_pending config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_unfinished_children_pending.
  now apply echo_ir_remove_preserves_unfinished_children_pending.
Qed.

Lemma echo_ir_root_request_unfinished_children_pending
    config state successor message certificates :
  echo_ir_unfinished_children_pending config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_unfinished_children_pending.
  now apply echo_ir_remove_preserves_unfinished_children_pending.
Qed.

Lemma echo_ir_remove_pending_update_preserves_unfinished_child
    config state (selected : ir_message node echo_ir_signature)
    owner new_parent new_finished child parent :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  owner = ir_message_receiver selected ->
  In child (ir_config_nodes config) ->
  echo_ir_parent_value node state child = Some parent ->
  echo_ir_finished_value node state child = false ->
  In child
    (echo_ir_pending_value node
      (echo_ir_update_process node node_eq state owner
        (IROptionNodeValue new_parent)
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender selected)
            (echo_ir_pending_value node state owner)))
        new_finished) parent).
Proof.
  intros invariant parent_replies selected_in reply_kind owner_receiver
    child_in child_parent child_unfinished.
  pose proof (invariant child parent child_in child_parent child_unfinished)
    as pending.
  destruct (node_eq owner parent) as [same_parent | parent_different].
  - subst parent.
    rewrite echo_ir_update_process_pending_same.
    apply echo_ir_remove_node_preserves_other.
    + intro same_child.
      subst child.
      pose proof (parent_replies selected selected_in reply_kind) as finished.
      assert (parent_link : echo_ir_parent_value node state
        (ir_message_sender selected) =
        Some (ir_message_receiver selected)).
      { now rewrite child_parent, <- owner_receiver. }
      specialize (finished parent_link).
      rewrite child_unfinished in finished. discriminate.
    + exact pending.
  - unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process
      by exact parent_different.
    exact pending.
Qed.

Lemma echo_ir_empty_pending_update_preserves_other_unfinished_child
    config state (selected : ir_message node echo_ir_signature)
    owner new_parent new_finished child parent :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  owner = ir_message_receiver selected ->
  ir_remove_node node_eq (ir_message_sender selected)
    (echo_ir_pending_value node state owner) = [] ->
  In child (ir_config_nodes config) ->
  child <> owner ->
  echo_ir_parent_value node state child = Some parent ->
  echo_ir_finished_value node state child = false ->
  In child
    (echo_ir_pending_value node
      (echo_ir_update_process node node_eq state owner
        (IROptionNodeValue new_parent) (IRListNodeValue [])
        new_finished) parent).
Proof.
  intros invariant parent_replies selected_in reply_kind owner_receiver empty
    child_in child_owner child_parent child_unfinished.
  pose proof (invariant child parent child_in child_parent child_unfinished)
    as pending.
  destruct (node_eq owner parent) as [same_parent | parent_different].
  - subst parent. exfalso.
    destruct (node_eq child (ir_message_sender selected))
      as [same_child | child_different].
    + subst child.
      pose proof (parent_replies selected selected_in reply_kind) as finished.
      assert (parent_link : echo_ir_parent_value node state
        (ir_message_sender selected) =
        Some (ir_message_receiver selected)).
      { now rewrite child_parent, <- owner_receiver. }
      specialize (finished parent_link).
      rewrite child_unfinished in finished. discriminate.
    + pose proof (echo_ir_remove_node_preserves_other
        (ir_message_sender selected) child
        (echo_ir_pending_value node state owner) child_different pending)
        as remains.
      rewrite empty in remains. contradiction.
  - unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process
      by exact parent_different.
    exact pending.
Qed.

Lemma echo_ir_participant_more_unfinished_children_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  echo_ir_finished_value node state (ir_message_receiver message) = false ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros invariant parent_replies queued reply_kind receiver_in
    unfinished action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    assert (old_parent : echo_ir_parent_value node state
      (ir_message_receiver message) = Some parent_node).
    { unfold echo_ir_parent_value. rewrite parent_value. reflexivity. }
    apply echo_ir_remove_preserves_unfinished_children_pending.
    apply echo_ir_update_preserves_unfinished_children_pending.
    + exact invariant.
    + intros parent owner_in parent_link new_unfinished.
      injection parent_link as <-.
      eapply echo_ir_remove_pending_update_preserves_unfinished_child;
        eauto; reflexivity.
    + intros child parent child_in child_owner child_parent child_unfinished.
      eapply echo_ir_remove_pending_update_preserves_unfinished_child;
        eauto; reflexivity.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_unfinished_children_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state (ir_message_receiver message)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros invariant parent_replies queued reply_kind empty action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    change (echo_ir_unfinished_children_pending config
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_unfinished_children_pending.
    apply echo_ir_remove_preserves_unfinished_children_pending.
    apply echo_ir_update_preserves_unfinished_children_pending.
    + exact invariant.
    + intros parent owner_in parent_link unfinished. discriminate.
    + intros child parent child_in child_owner child_parent child_unfinished.
      apply echo_ir_empty_pending_update_preserves_other_unfinished_child
        with (config := config) (state := state) (selected := message);
        try assumption.
      reflexivity.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_unfinished_children_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros invariant parent_replies queued reply_kind receiver_root action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_unfinished_children_pending.
  apply echo_ir_update_preserves_unfinished_children_pending.
  - exact invariant.
  - intros parent owner_in parent_link unfinished. discriminate.
  - intros child parent child_in child_owner child_parent child_unfinished.
    eapply echo_ir_remove_pending_update_preserves_unfinished_child.
    + exact invariant.
    + exact parent_replies.
    + exact queued.
    + exact reply_kind.
    + now symmetry.
    + exact child_in.
    + exact child_parent.
    + exact child_unfinished.
Qed.

Lemma echo_ir_initiator_final_unfinished_children_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros invariant parent_replies queued reply_kind receiver_root empty action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_unfinished_children_pending.
  apply echo_ir_update_preserves_unfinished_children_pending.
  - exact invariant.
  - intros parent owner_in parent_link unfinished. discriminate.
  - intros child parent child_in child_owner child_parent child_unfinished.
    eapply echo_ir_empty_pending_update_preserves_other_unfinished_child.
    + exact invariant.
    + exact parent_replies.
    + exact queued.
    + exact reply_kind.
    + now symmetry.
    + exact empty.
    + exact child_in.
    + exact child_owner.
    + exact child_parent.
    + exact child_unfinished.
Qed.

Theorem EchoStep_preserves_unfinished_children_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_request_senders_provenanced node config state ->
  echo_ir_parent_sources_provenanced node config state ->
  echo_ir_queued_edges_valid node config state ->
  echo_ir_queued_requests_pending state ->
  echo_ir_parent_replies_from_finished state ->
  echo_ir_unfinished_children_pending config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_unfinished_children_pending config successor.
Proof.
  intros request_senders parent_sources queued_edges requests parent_replies
    invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_unfinished_children_pending.
    + now apply (echo_ir_start_enabled_configured_parent_none node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
        message certificates (@echo_ir_first_request_nonleaf_rule node)
        enabled ltac:(cbn [echo_ir_first_request_nonleaf_rule]; now left))
        as nonroot.
      pose proof (echo_ir_first_nonleaf_enabled_parent_none node node_eq
        config state message certificates enabled) as no_parent.
      pose proof (echo_ir_resolved_delivery_queued node state
        external_event message certificates resolved) as queued.
      pose proof (echo_ir_enabled_request_pattern_kind node node_eq
        config state message certificates
        (@echo_ir_first_request_nonleaf_rule node) eq_refl enabled)
        as request_kind.
      eapply echo_ir_nonleaf_unfinished_children_pending; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
          message certificates (@echo_ir_first_request_leaf_rule node)
          enabled ltac:(cbn [echo_ir_first_request_leaf_rule]; now left))
          as nonroot.
        pose proof (echo_ir_enabled_receiver_parent_none config state message
          certificates (@echo_ir_first_request_leaf_rule node) enabled
          ltac:(cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
            now right; left)) as no_parent.
        eapply echo_ir_leaf_unfinished_children_pending; eauto.
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_repeated_unfinished_children_pending; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              eapply echo_ir_root_request_unfinished_children_pending; eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 pose proof (echo_ir_resolved_delivery_queued node state
                   external_event message certificates resolved) as queued.
                 pose proof (echo_ir_enabled_reply_pattern_kind config state
                   message certificates
                   (@echo_ir_participant_reply_more_rule node) eq_refl enabled)
                   as reply_kind.
                 pose proof (echo_ir_enabled_expected_parent node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)) as old_parent.
                 pose proof (echo_ir_enabled_receiver_unfinished config state
                   message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     repeat (first [left; reflexivity | right])))
                   as unfinished.
                 destruct (queued_edges message queued) as
                   [sender_in [receiver_in edge]].
                 eapply echo_ir_participant_more_unfinished_children_pending;
                   eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     pose proof (echo_ir_resolved_delivery_queued node state
                       external_event message certificates resolved) as queued.
                     pose proof (echo_ir_enabled_reply_pattern_kind config state
                       message certificates
                       (@echo_ir_participant_reply_final_rule node)
                       eq_refl enabled) as reply_kind.
                     pose proof
                       (echo_ir_enabled_receiver_removed_pending_empty config
                         state message certificates
                         (@echo_ir_participant_reply_final_rule node) enabled
                         ltac:(cbn [echo_ir_participant_reply_final_rule];
                           repeat (first [left; reflexivity | right])))
                       as empty.
                     eapply
                       echo_ir_participant_final_unfinished_children_pending;
                       eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         pose proof (echo_ir_resolved_delivery_queued node state
                           external_event message certificates resolved)
                           as queued.
                         pose proof (echo_ir_enabled_reply_pattern_kind config
                           state message certificates
                           (@echo_ir_initiator_reply_more_rule node)
                           eq_refl enabled) as reply_kind.
                         pose proof (echo_ir_enabled_initiator_receiver node
                           node_eq config state message certificates
                           (@echo_ir_initiator_reply_more_rule node) enabled
                           ltac:(cbn [echo_ir_initiator_reply_more_rule];
                             now left)) as receiver_root.
                         eapply
                           echo_ir_initiator_more_unfinished_children_pending;
                           eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             pose proof (echo_ir_resolved_delivery_queued node
                               state external_event message certificates
                               resolved) as queued.
                             pose proof
                               (echo_ir_enabled_reply_pattern_kind config state
                                 message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 eq_refl enabled) as reply_kind.
                             pose proof (echo_ir_enabled_initiator_receiver node
                               node_eq config state message certificates
                               (@echo_ir_initiator_reply_final_rule node) enabled
                               ltac:(cbn [echo_ir_initiator_reply_final_rule];
                                 now left)) as receiver_root.
                             pose proof
                               (echo_ir_enabled_initiator_removed_pending_empty
                                 config state message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 enabled
                                 ltac:(cbn [echo_ir_initiator_reply_final_rule];
                                   repeat
                                     (first [left; reflexivity | right])))
                               as empty.
                             eapply
                               echo_ir_initiator_final_unfinished_children_pending;
                               eauto.
                         *** contradiction.
Qed.

Definition echo_ir_child_pending_bundle config state : Prop :=
  echo_ir_request_pending_bundle config state /\
  echo_ir_unfinished_children_pending config state.

Lemma EchoStep_preserves_child_pending_bundle
    config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_child_pending_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_child_pending_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric
    [request_pending children] step.
  assert (request_pending_after :
    echo_ir_request_pending_bundle config successor).
  { eapply EchoStep_preserves_request_pending_bundle; eauto. }
  split; [exact request_pending_after |].
  destruct request_pending as [edge_bundle requests].
  destruct edge_bundle as [parent_bundle reply_unique].
  destruct parent_bundle as
    [request_bundle [root_parent [reply_discovery parent_replies]]].
  destruct request_bundle as
    [[parent_edges queued_edges]
      [discovered [accounting [reply_support reverse]]]].
  destruct accounting as
    [[request_unique request_senders]
      [message_ids [parent_sources request_parent_distinct]]].
  eapply EchoStep_preserves_unfinished_children_pending; eauto.
Qed.

Lemma echo_ir_initial_child_pending_bundle config :
  echo_ir_child_pending_bundle config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_request_pending_bundle.
  - apply echo_ir_initial_unfinished_children_pending.
Qed.

Theorem echo_ir_path_preserves_child_pending_bundle config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_child_pending_bundle config initial ->
  echo_ir_child_pending_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_child_pending_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_unfinished_children_pending config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_unfinished_children_pending config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_child_pending_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_child_pending_bundle config)) as bundle.
  exact (proj2 bundle).
Qed.

Definition echo_ir_queued_replies_pending
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    In (ir_message_sender message)
      (echo_ir_pending_value node state (ir_message_receiver message)).

Lemma echo_ir_remove_preserves_queued_replies_pending state selected_id :
  echo_ir_queued_replies_pending state ->
  echo_ir_queued_replies_pending
    (ir_remove_selected_message state selected_id).
Proof.
  intros invariant message queued reply_kind.
  apply invariant with (message := message); try assumption.
  cbn [ir_remove_selected_message ir_message_store] in queued.
  now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_update_preserves_queued_replies_pending
    state owner parent pending finished :
  echo_ir_queued_replies_pending state ->
  (forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    ir_message_receiver message = owner ->
    In (ir_message_sender message) pending) ->
  echo_ir_queued_replies_pending
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished).
Proof.
  intros invariant updated message queued reply_kind.
  destruct (node_eq owner (ir_message_receiver message))
    as [same | different].
  - subst owner.
    unfold echo_ir_pending_value, echo_ir_update_process.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    apply updated with (message := message); try assumption; reflexivity.
  - unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    now apply invariant with (message := message).
Qed.

Lemma echo_ir_emit_preserves_queued_replies_pending
    state kind sender receivers payload :
  echo_ir_queued_replies_pending state ->
  (kind = EchoIRReply ->
    forall receiver,
      In receiver receivers ->
      In sender (echo_ir_pending_value node state receiver)) ->
  echo_ir_queued_replies_pending
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros invariant emitted_pending message queued reply_kind.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - now apply invariant with (message := message).
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) kind sender receivers payload message emitted)
      as [same_sender receiver_in].
    pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload message emitted)
      as same_kind.
    rewrite reply_kind in same_kind. subst kind.
    rewrite same_sender.
    now apply emitted_pending.
Qed.

Lemma echo_ir_emit_nonreply_preserves_queued_replies_pending
    state kind sender receivers payload :
  echo_ir_queued_replies_pending state ->
  kind <> EchoIRReply ->
  echo_ir_queued_replies_pending
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros invariant not_reply.
  apply echo_ir_emit_preserves_queued_replies_pending.
  - exact invariant.
  - now intros reply_kind.
Qed.

Lemma echo_ir_initial_queued_replies_pending :
  echo_ir_queued_replies_pending (@echo_initial_state node).
Proof. intros message queued. contradiction. Qed.

Lemma echo_ir_start_queued_replies_pending config state successor certificates :
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros empty action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  apply echo_ir_emit_nonreply_preserves_queued_replies_pending.
  - apply echo_ir_update_preserves_queued_replies_pending.
    + intros message queued. rewrite empty in queued. contradiction.
    + intros message queued. rewrite empty in queued. contradiction.
  - discriminate.
Qed.

Lemma echo_ir_initial_receiver_has_no_queued_replies
    config state owner :
  echo_ir_reply_receivers_discovered node state ->
  echo_ir_discovered_participants_parented node config state ->
  owner <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state owner = None ->
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    ir_message_receiver message = owner ->
    False.
Proof.
  intros receivers parented nonroot no_parent message queued reply_kind receiver.
  pose proof (receivers message queued reply_kind) as discovered.
  rewrite receiver in discovered.
  destruct (parented owner nonroot discovered) as [parent installed].
  rewrite no_parent in installed. discriminate.
Qed.

Lemma echo_ir_remaining_reply_sender_pending_after_selected_removal
    state (selected : ir_message node echo_ir_signature) :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  forall message,
    In message
      (ir_remove_message (ir_message_id selected) (ir_message_store state)) ->
    ir_message_kind message = EchoIRReply ->
    ir_message_receiver message = ir_message_receiver selected ->
    In (ir_message_sender message)
      (ir_remove_node node_eq (ir_message_sender selected)
        (echo_ir_pending_value node state (ir_message_receiver selected))).
Proof.
  intros [_ ids_nodup] unique invariant selected_in selected_kind
    message remaining reply_kind same_receiver.
  pose proof (echo_ir_remove_message_in node
    (ir_message_id selected) _ message remaining) as queued.
  pose proof (invariant message queued reply_kind) as pending.
  rewrite same_receiver in pending.
  destruct (node_eq (ir_message_sender message)
    (ir_message_sender selected)) as [same_sender | different].
  - assert (same_message : message = selected).
    { eapply unique; eauto. }
    subst message.
    exfalso. exact (echo_ir_remove_message_selected_not_in node selected
      (ir_message_store state) ids_nodup remaining).
  - now apply echo_ir_remove_node_preserves_other.
Qed.

(** Consuming a reply and removing its sender from the receiver's pending
    list preserves the queued-reply invariant.  Reply-edge uniqueness is the
    key fact: no different queued reply for the same receiver can have the
    consumed sender. *)
Lemma echo_ir_remove_preserves_pending_value state selected_id owner :
  echo_ir_pending_value node
    (ir_remove_selected_message state selected_id) owner =
  echo_ir_pending_value node state owner.
Proof. reflexivity. Qed.

Lemma echo_ir_update_remove_reply_preserves_queued_replies_pending
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    owner parent finished :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  owner = ir_message_receiver selected ->
  echo_ir_queued_replies_pending
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state owner parent
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender selected)
            (echo_ir_pending_value node state owner)))
        finished)
      (ir_message_id selected)).
Proof.
  intros ids unique invariant selected_in selected_kind owner_receiver
    message remaining reply_kind.
  change (In message
    (ir_remove_message (ir_message_id selected)
      (ir_message_store state))) in remaining.
  rewrite echo_ir_remove_preserves_pending_value.
  destruct (node_eq owner (ir_message_receiver message))
    as [same | different].
  - subst owner.
    rewrite <- same.
    unfold echo_ir_pending_value, echo_ir_update_process.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    eapply echo_ir_remaining_reply_sender_pending_after_selected_removal;
      eauto.
  - unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    apply invariant with (message := message); try assumption.
    now apply (echo_ir_remove_message_in node
      (ir_message_id selected) _ message).
Qed.

Lemma echo_ir_nonleaf_queued_replies_pending
    config state successor message certificates :
  echo_ir_reply_receivers_discovered node state ->
  echo_ir_discovered_participants_parented node config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  echo_ir_queued_replies_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros receivers parented nonroot no_parent invariant action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_nonreply_preserves_queued_replies_pending.
  - apply echo_ir_remove_preserves_queued_replies_pending.
    apply echo_ir_update_preserves_queued_replies_pending.
    + exact invariant.
    + intros reply queued reply_kind same_receiver. exfalso.
      eapply echo_ir_initial_receiver_has_no_queued_replies; eauto.
  - discriminate.
Qed.

Lemma echo_ir_leaf_queued_replies_pending
    config state successor message certificates :
  echo_ir_request_senders_provenanced node config state ->
  echo_ir_reply_receivers_discovered node state ->
  echo_ir_discovered_participants_parented node config state ->
  ir_message_receiver message <> echo_ir_config_initiator node config ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_queued_requests_pending state ->
  echo_ir_queued_replies_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros senders receivers parented nonroot no_parent queued request_kind
    requests invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_queued_replies_pending.
  - apply echo_ir_remove_preserves_queued_replies_pending.
    apply echo_ir_update_preserves_queued_replies_pending.
    + exact invariant.
    + intros reply reply_in reply_kind same_receiver. exfalso.
      eapply echo_ir_initial_receiver_has_no_queued_replies; eauto.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    assert (different : ir_message_receiver message <>
      ir_message_sender message).
    { intro equal.
      eapply echo_ir_unparented_noninitiator_has_no_queued_requests
        with (message := message); eauto. }
    pose proof (requests message queued request_kind) as pending.
    change (In (ir_message_receiver message)
      (echo_ir_pending_value node
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some (ir_message_sender message)))
          (IRListNodeValue []) true)
        (ir_message_sender message))).
    unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    exact pending.
Qed.

Lemma echo_ir_repeated_queued_replies_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_queued_requests_pending state ->
  echo_ir_queued_replies_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros queued request_kind requests invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_queued_replies_pending.
  - now apply echo_ir_remove_preserves_queued_replies_pending.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    exact (requests message queued request_kind).
Qed.

Lemma echo_ir_root_request_queued_replies_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  echo_ir_queued_requests_pending state ->
  echo_ir_queued_replies_pending state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros queued request_kind receiver_root requests invariant action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_queued_replies_pending.
  - now apply echo_ir_remove_preserves_queued_replies_pending.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    unfold echo_ir_config_initiator in receiver_root.
    rewrite <- receiver_root.
    exact (requests message queued request_kind).
Qed.

Lemma echo_ir_update_empty_remove_reply_preserves_queued_replies_pending
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    owner parent finished :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRReply ->
  owner = ir_message_receiver selected ->
  ir_remove_node node_eq (ir_message_sender selected)
    (echo_ir_pending_value node state owner) = [] ->
  echo_ir_queued_replies_pending
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state owner parent
        (IRListNodeValue []) finished)
      (ir_message_id selected)).
Proof.
  intros ids unique invariant selected_in selected_kind owner_receiver empty
    message remaining reply_kind.
  change (In message
    (ir_remove_message (ir_message_id selected)
      (ir_message_store state))) in remaining.
  rewrite echo_ir_remove_preserves_pending_value.
  destruct (node_eq owner (ir_message_receiver message))
    as [same | different].
  - subst owner. rewrite <- same.
    unfold echo_ir_pending_value, echo_ir_update_process.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    exfalso.
    pose proof
      (echo_ir_remaining_reply_sender_pending_after_selected_removal
        state selected ids unique invariant selected_in selected_kind
        message remaining reply_kind (eq_sym same)) as pending.
    rewrite empty in pending. contradiction.
  - unfold echo_ir_pending_value, echo_ir_update_process.
    repeat rewrite ir_set_local_field_read_other_process by exact different.
    apply invariant with (message := message); try assumption.
    now apply (echo_ir_remove_message_in node
      (ir_message_id selected) _ message).
Qed.

Lemma echo_ir_participant_more_queued_replies_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros ids unique invariant queued reply_kind action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    eapply echo_ir_update_remove_reply_preserves_queued_replies_pending;
      eauto.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_queued_replies_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros ids unique invariant queued reply_kind receiver_root action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_update_remove_reply_preserves_queued_replies_pending;
    eauto.
Qed.

Lemma echo_ir_participant_final_queued_replies_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_replies_from_finished state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  echo_ir_finished_value node state (ir_message_receiver message) = false ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state (ir_message_receiver message)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros ids unique invariant children parent_replies queued reply_kind
    receiver_in unfinished empty action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    assert (old_parent : echo_ir_parent_value node state
      (ir_message_receiver message) = Some parent_node).
    { unfold echo_ir_parent_value. rewrite parent_value. reflexivity. }
    change (echo_ir_queued_replies_pending
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_queued_replies_pending.
    + eapply echo_ir_update_empty_remove_reply_preserves_queued_replies_pending;
        eauto.
    + intros _ receiver [same_receiver | impossible];
        [subst receiver | contradiction].
      assert (different_parent : ir_message_receiver message <> parent_node).
      { intro same_parent.
        pose proof (children (ir_message_receiver message) parent_node
          receiver_in old_parent unfinished) as pending.
        destruct (node_eq (ir_message_receiver message)
          (ir_message_sender message)) as [same_sender | different_sender].
        - pose proof (parent_replies message queued reply_kind) as finished.
          assert (parent_link : echo_ir_parent_value node state
            (ir_message_sender message) = Some (ir_message_receiver message)).
          { rewrite <- same_sender, old_parent. now rewrite <- same_parent. }
          specialize (finished parent_link).
          rewrite <- same_sender in finished.
          rewrite unfinished in finished. discriminate.
        - pose proof (echo_ir_remove_node_preserves_other
            (ir_message_sender message) (ir_message_receiver message)
            (echo_ir_pending_value node state parent_node)
            different_sender pending) as remains.
          rewrite <- same_parent, empty in remains. contradiction. }
      rewrite echo_ir_remove_preserves_pending_value.
      unfold echo_ir_pending_value, echo_ir_update_process.
      repeat rewrite ir_set_local_field_read_other_process
        by exact different_parent.
      exact (children (ir_message_receiver message) parent_node
        receiver_in old_parent unfinished).
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_final_queued_replies_pending
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_replies_pending state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros ids unique invariant queued reply_kind receiver_root empty action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_update_empty_remove_reply_preserves_queued_replies_pending;
    eauto.
Qed.

Theorem EchoStep_preserves_queued_replies_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_request_senders_provenanced node config state ->
  echo_ir_discovered_participants_parented node config state ->
  echo_ir_reply_receivers_discovered node state ->
  echo_ir_message_ids_well_formed node state ->
  echo_ir_reply_edges_unique state ->
  echo_ir_queued_edges_valid node config state ->
  echo_ir_queued_requests_pending state ->
  echo_ir_parent_replies_from_finished state ->
  echo_ir_unfinished_children_pending config state ->
  echo_ir_queued_replies_pending state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_queued_replies_pending successor.
Proof.
  intros request_senders parented reply_receivers ids unique queued_edges
    requests parent_replies children invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_queued_replies_pending.
    + now apply (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
        message certificates (@echo_ir_first_request_nonleaf_rule node)
        enabled ltac:(cbn [echo_ir_first_request_nonleaf_rule]; now left))
        as nonroot.
      pose proof (echo_ir_first_nonleaf_enabled_parent_none node node_eq
        config state message certificates enabled) as no_parent.
      eapply echo_ir_nonleaf_queued_replies_pending; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
          message certificates (@echo_ir_first_request_leaf_rule node)
          enabled ltac:(cbn [echo_ir_first_request_leaf_rule]; now left))
          as nonroot.
        pose proof (echo_ir_enabled_receiver_parent_none config state message
          certificates (@echo_ir_first_request_leaf_rule node) enabled
          ltac:(cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
            now right; left)) as no_parent.
        pose proof (echo_ir_resolved_delivery_queued node state
          external_event message certificates resolved) as queued.
        pose proof (echo_ir_enabled_request_pattern_kind node node_eq
          config state message certificates
          (@echo_ir_first_request_leaf_rule node) eq_refl enabled)
          as request_kind.
        eapply echo_ir_leaf_queued_replies_pending; eauto.
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           pose proof (echo_ir_resolved_delivery_queued node state
             external_event message certificates resolved) as queued.
           pose proof (echo_ir_enabled_request_pattern_kind node node_eq
             config state message certificates
             (@echo_ir_repeated_request_rule node) eq_refl enabled)
             as request_kind.
           eapply echo_ir_repeated_queued_replies_pending; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              pose proof (echo_ir_resolved_delivery_queued node state
                external_event message certificates resolved) as queued.
              pose proof (echo_ir_enabled_request_pattern_kind node node_eq
                config state message certificates
                (@echo_ir_initiator_request_rule node) eq_refl enabled)
                as request_kind.
              pose proof (echo_ir_enabled_initiator_receiver node node_eq
                config state message certificates
                (@echo_ir_initiator_request_rule node) enabled
                ltac:(cbn [echo_ir_initiator_request_rule]; now left))
                as receiver_root.
              eapply echo_ir_root_request_queued_replies_pending; eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 pose proof (echo_ir_resolved_delivery_queued node state
                   external_event message certificates resolved) as queued.
                 pose proof (echo_ir_enabled_reply_pattern_kind config state
                   message certificates
                   (@echo_ir_participant_reply_more_rule node) eq_refl enabled)
                   as reply_kind.
                 eapply echo_ir_participant_more_queued_replies_pending;
                   eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     pose proof (echo_ir_resolved_delivery_queued node state
                       external_event message certificates resolved) as queued.
                     pose proof (echo_ir_enabled_reply_pattern_kind config state
                       message certificates
                       (@echo_ir_participant_reply_final_rule node)
                       eq_refl enabled) as reply_kind.
                     pose proof (echo_ir_enabled_expected_parent node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)) as old_parent.
                     pose proof (echo_ir_enabled_receiver_unfinished config state
                       message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         repeat (first [left; reflexivity | right])))
                       as unfinished.
                     pose proof
                       (echo_ir_enabled_receiver_removed_pending_empty config
                         state message certificates
                         (@echo_ir_participant_reply_final_rule node) enabled
                         ltac:(cbn [echo_ir_participant_reply_final_rule];
                           repeat (first [left; reflexivity | right])))
                       as empty.
                     destruct (queued_edges message queued) as
                       [sender_in [receiver_in edge]].
                     eapply echo_ir_participant_final_queued_replies_pending;
                       eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         pose proof (echo_ir_resolved_delivery_queued node state
                           external_event message certificates resolved)
                           as queued.
                         pose proof (echo_ir_enabled_reply_pattern_kind config
                           state message certificates
                           (@echo_ir_initiator_reply_more_rule node)
                           eq_refl enabled) as reply_kind.
                         pose proof (echo_ir_enabled_initiator_receiver node
                           node_eq config state message certificates
                           (@echo_ir_initiator_reply_more_rule node) enabled
                           ltac:(cbn [echo_ir_initiator_reply_more_rule];
                             now left)) as receiver_root.
                         eapply echo_ir_initiator_more_queued_replies_pending;
                           eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             pose proof (echo_ir_resolved_delivery_queued node
                               state external_event message certificates
                               resolved) as queued.
                             pose proof
                               (echo_ir_enabled_reply_pattern_kind config state
                                 message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 eq_refl enabled) as reply_kind.
                             pose proof (echo_ir_enabled_initiator_receiver node
                               node_eq config state message certificates
                               (@echo_ir_initiator_reply_final_rule node) enabled
                               ltac:(cbn [echo_ir_initiator_reply_final_rule];
                                 now left)) as receiver_root.
                             pose proof
                               (echo_ir_enabled_initiator_removed_pending_empty
                                 config state message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 enabled
                                 ltac:(cbn [echo_ir_initiator_reply_final_rule];
                                   repeat
                                     (first [left; reflexivity | right])))
                               as empty.
                             eapply
                               echo_ir_initiator_final_queued_replies_pending;
                               eauto.
                         *** contradiction.
Qed.

Definition echo_ir_reply_pending_bundle config state : Prop :=
  echo_ir_child_pending_bundle config state /\
  echo_ir_queued_replies_pending state.

Lemma EchoStep_preserves_reply_pending_bundle
    config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_reply_pending_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_reply_pending_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric [child_bundle replies] step.
  assert (child_after : echo_ir_child_pending_bundle config successor).
  { eapply EchoStep_preserves_child_pending_bundle; eauto. }
  split; [exact child_after |].
  destruct child_bundle as [request_pending children].
  destruct request_pending as [edge_bundle requests].
  destruct edge_bundle as [parent_bundle reply_unique].
  destruct parent_bundle as
    [request_bundle [root_parent [reply_discovery parent_replies]]].
  destruct request_bundle as
    [[parent_edges queued_edges]
      [discovered [accounting [reply_support reverse]]]].
  destruct accounting as
    [[request_unique request_senders]
      [message_ids [parent_sources request_parent_distinct]]].
  destruct reply_support as
    [parent_targets [request_receivers reply_receivers]].
  eapply EchoStep_preserves_queued_replies_pending; eauto.
Qed.

Lemma echo_ir_initial_reply_pending_bundle config :
  echo_ir_reply_pending_bundle config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_child_pending_bundle.
  - apply echo_ir_initial_queued_replies_pending.
Qed.

Theorem echo_ir_path_preserves_reply_pending_bundle config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_reply_pending_bundle config initial ->
  echo_ir_reply_pending_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_reply_pending_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_queued_replies_pending config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_queued_replies_pending state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_reply_pending_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_reply_pending_bundle config)) as bundle.
  exact (proj2 bundle).
Qed.

(** A finished process has discharged every pending obligation.  Keeping this
    invariant in the direct executable layer is a prerequisite for following
    a nonempty pending obligation through the parent chain. *)
Definition echo_ir_completion_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_finished_value node state owner = true ->
    echo_ir_pending_value node state owner = [].

Lemma echo_ir_update_process_preserves_completion
    config state owner parent pending finished :
  echo_ir_completion_well_formed config state ->
  (finished = true -> pending = []) ->
  echo_ir_completion_well_formed config
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished).
Proof.
  intros invariant new_valid observed observed_in observed_finished.
  destruct (node_eq owner observed) as [same | different].
  - subst observed.
    unfold echo_ir_finished_value, echo_ir_pending_value,
      echo_ir_update_process in observed_finished |- *.
    rewrite ir_set_local_field_same in observed_finished.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    now apply new_valid.
  - unfold echo_ir_finished_value, echo_ir_pending_value,
      echo_ir_update_process in observed_finished |- *.
    repeat rewrite ir_set_local_field_read_other_process
      in observed_finished by exact different.
    repeat rewrite ir_set_local_field_read_other_process
      by exact different.
    now apply invariant with (owner := observed).
Qed.

Lemma echo_ir_processes_preserve_completion config left right :
  echo_ir_completion_well_formed config left ->
  ir_processes right = ir_processes left ->
  echo_ir_completion_well_formed config right.
Proof.
  intros invariant processes owner owner_in finished.
  unfold echo_ir_finished_value in finished.
  unfold echo_ir_pending_value.
  rewrite processes in finished |- *.
  now apply invariant with (owner := owner).
Qed.

Lemma echo_ir_remove_preserves_completion config state selected_id :
  echo_ir_completion_well_formed config state ->
  echo_ir_completion_well_formed config
    (ir_remove_selected_message state selected_id).
Proof.
  intro invariant.
  eapply echo_ir_processes_preserve_completion; [exact invariant | reflexivity].
Qed.

Lemma echo_ir_emit_preserves_completion
    config state kind sender receivers payload :
  echo_ir_completion_well_formed config state ->
  echo_ir_completion_well_formed config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intro invariant.
  eapply echo_ir_processes_preserve_completion; [exact invariant | reflexivity].
Qed.

Lemma echo_ir_set_global_preserves_completion config state field value :
  echo_ir_completion_well_formed config state ->
  echo_ir_completion_well_formed config
    (ir_set_global_field state field value).
Proof.
  intro invariant.
  eapply echo_ir_processes_preserve_completion; [exact invariant | reflexivity].
Qed.

Lemma echo_ir_initial_completion config :
  echo_ir_completion_well_formed config (@echo_initial_state node).
Proof.
  intros owner owner_in finished. discriminate.
Qed.

Lemma echo_ir_start_completion config state successor certificates :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_completion.
  apply echo_ir_set_global_preserves_completion.
  apply echo_ir_update_process_preserves_completion.
  - exact invariant.
  - discriminate.
Qed.

Lemma echo_ir_nonleaf_completion config state successor message certificates :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_completion.
  apply echo_ir_remove_preserves_completion.
  apply echo_ir_update_process_preserves_completion.
  - exact invariant.
  - discriminate.
Qed.

Lemma echo_ir_leaf_completion config state successor message certificates :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_completion.
  apply echo_ir_remove_preserves_completion.
  apply echo_ir_update_process_preserves_completion.
  - exact invariant.
  - reflexivity.
Qed.

Lemma echo_ir_repeated_completion config state successor message certificates :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_completion.
  now apply echo_ir_remove_preserves_completion.
Qed.

Lemma echo_ir_root_request_completion
    config state successor message certificates :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_completion.
  now apply echo_ir_remove_preserves_completion.
Qed.

Lemma echo_ir_participant_more_completion
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    apply echo_ir_remove_preserves_completion.
    apply echo_ir_update_process_preserves_completion.
    + exact invariant.
    + discriminate.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_completion
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    change (echo_ir_completion_well_formed config
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_completion.
    apply echo_ir_remove_preserves_completion.
    apply echo_ir_update_process_preserves_completion.
    + exact invariant.
    + reflexivity.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_completion
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_completion.
  apply echo_ir_update_process_preserves_completion.
  - exact invariant.
  - discriminate.
Qed.

Lemma echo_ir_initiator_final_completion
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_completion_well_formed config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_completion.
  apply echo_ir_update_process_preserves_completion.
  - exact invariant.
  - reflexivity.
Qed.

Theorem EchoStep_preserves_completion
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_completion_well_formed config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_completion_well_formed config successor.
Proof.
  intros invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_completion; eauto.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      eapply echo_ir_nonleaf_completion; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        eapply echo_ir_leaf_completion; eauto.
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_repeated_completion; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              eapply echo_ir_root_request_completion; eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 eapply echo_ir_participant_more_completion; eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     eapply echo_ir_participant_final_completion; eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         eapply echo_ir_initiator_more_completion; eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             eapply echo_ir_initiator_final_completion; eauto.
                         *** contradiction.
Qed.

Theorem echo_ir_path_preserves_completion config initial final :
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_completion_well_formed config initial ->
  echo_ir_completion_well_formed config final.
Proof.
  intro reachable.
  induction reachable; intro invariant.
  - exact invariant.
  - apply IHreachable.
    eapply EchoStep_preserves_completion.
    + exact invariant.
    + exists rule. exact H.
Qed.

Theorem echo_reachable_completion config state :
  echo_reachable node node_eq config state ->
  echo_ir_completion_well_formed config state.
Proof.
  intro reachable.
  eapply echo_ir_path_preserves_completion.
  - exact reachable.
  - apply echo_ir_initial_completion.
Qed.

(** Proof-only certificate that following installed parent pointers reaches the
    configured initiator.  No rank or path data is added to the executable IR
    state or to the generated Python artifact. *)
Inductive echo_ir_parent_chain
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : node -> Prop :=
  | EchoIRParentChainRoot :
      echo_ir_parent_chain config state
        (echo_ir_config_initiator node config)
  | EchoIRParentChainStep : forall child parent,
      In child (ir_config_nodes config) ->
      echo_ir_parent_value node state child = Some parent ->
      echo_ir_parent_chain config state parent ->
      echo_ir_parent_chain config state child.

Definition echo_ir_parent_chains_rooted
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall child parent,
    In child (ir_config_nodes config) ->
    echo_ir_parent_value node state child = Some parent ->
    echo_ir_parent_chain config state child.

Lemma echo_ir_parent_chain_ext config left right owner :
  (forall observed,
    echo_ir_parent_value node right observed =
    echo_ir_parent_value node left observed) ->
  echo_ir_parent_chain config left owner ->
  echo_ir_parent_chain config right owner.
Proof.
  intros parents chain. induction chain.
  - constructor.
  - eapply EchoIRParentChainStep.
    + exact H.
    + rewrite parents. exact H0.
    + exact IHchain.
Qed.

Lemma echo_ir_parent_chains_rooted_ext config left right :
  echo_ir_parent_chains_rooted config left ->
  (forall observed,
    echo_ir_parent_value node right observed =
    echo_ir_parent_value node left observed) ->
  echo_ir_parent_chains_rooted config right.
Proof.
  intros rooted parents child parent child_in parent_link.
  apply echo_ir_parent_chain_ext with (left := left).
  - exact parents.
  - apply rooted with (parent := parent); [exact child_in |].
    now rewrite <- parents.
Qed.

Lemma echo_ir_remove_preserves_parent_chains_rooted
    config state selected_id :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_chains_rooted config
    (ir_remove_selected_message state selected_id).
Proof.
  intro rooted. eapply echo_ir_parent_chains_rooted_ext.
  - exact rooted.
  - reflexivity.
Qed.

Lemma echo_ir_emit_preserves_parent_chains_rooted
    config state kind sender receivers payload :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_chains_rooted config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intro rooted. eapply echo_ir_parent_chains_rooted_ext.
  - exact rooted.
  - reflexivity.
Qed.

Lemma echo_ir_set_global_preserves_parent_chains_rooted
    config state field value :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_chains_rooted config
    (ir_set_global_field state field value).
Proof.
  intro rooted. eapply echo_ir_parent_chains_rooted_ext.
  - exact rooted.
  - reflexivity.
Qed.

Lemma echo_ir_update_parent_value_same
    state owner parent pending finished :
  echo_ir_parent_value node
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue parent) pending finished) owner = parent.
Proof.
  unfold echo_ir_parent_value, echo_ir_update_process.
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_same. reflexivity.
Qed.

Lemma echo_ir_update_parent_value_other
    state owner parent pending finished observed :
  owner <> observed ->
  echo_ir_parent_value node
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue parent) pending finished) observed =
  echo_ir_parent_value node state observed.
Proof.
  intro different.
  unfold echo_ir_parent_value, echo_ir_update_process.
  repeat rewrite ir_set_local_field_read_other_process by exact different.
  reflexivity.
Qed.

Lemma echo_ir_update_same_parent_preserves_parent_chains_rooted
    config state owner parent pending finished :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state owner = parent ->
  echo_ir_parent_chains_rooted config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue parent) pending finished).
Proof.
  intros rooted old_parent.
  eapply echo_ir_parent_chains_rooted_ext.
  - exact rooted.
  - intro observed. destruct (node_eq owner observed) as [same | different].
    + subst observed. rewrite echo_ir_update_parent_value_same.
      now symmetry.
    + now apply echo_ir_update_parent_value_other.
Qed.

Lemma echo_ir_parent_chain_survives_install
    config state owner parent pending finished observed :
  echo_ir_parent_value node state owner = None ->
  echo_ir_parent_chain config state observed ->
  echo_ir_parent_chain config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished) observed.
Proof.
  intros owner_initial chain. induction chain.
  - constructor.
  - eapply EchoIRParentChainStep.
    + exact H.
    + destruct (node_eq owner child) as [same | different].
      * subst child. rewrite owner_initial in H0. discriminate.
      * rewrite echo_ir_update_parent_value_other by exact different.
        exact H0.
    + exact IHchain.
Qed.

Lemma echo_ir_install_parent_preserves_parent_chains_rooted
    config state owner parent pending finished :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state owner = None ->
  In owner (ir_config_nodes config) ->
  echo_ir_parent_chain config state parent ->
  echo_ir_parent_chains_rooted config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished).
Proof.
  intros rooted owner_initial owner_in parent_chain
    child installed child_in parent_link.
  destruct (node_eq owner child) as [same | different].
  - subst child.
    rewrite echo_ir_update_parent_value_same in parent_link.
    injection parent_link as <-.
    eapply EchoIRParentChainStep.
    + exact owner_in.
    + apply echo_ir_update_parent_value_same.
    + now apply echo_ir_parent_chain_survives_install.
  - rewrite echo_ir_update_parent_value_other in parent_link
      by exact different.
    apply echo_ir_parent_chain_survives_install.
    + exact owner_initial.
    + now apply rooted with (parent := installed).
Qed.

Lemma echo_ir_initial_parent_chains_rooted config :
  echo_ir_parent_chains_rooted config (@echo_initial_state node).
Proof.
  intros child parent child_in parent_link. discriminate.
Qed.

Lemma echo_ir_start_parent_chains_rooted
    config state successor certificates :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state
    (echo_ir_config_initiator node config) = None ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted root_parent action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_chains_rooted.
  apply echo_ir_set_global_preserves_parent_chains_rooted.
  apply echo_ir_update_same_parent_preserves_parent_chains_rooted.
  - exact rooted.
  - exact root_parent.
Qed.

Lemma echo_ir_nonleaf_parent_chains_rooted
    config state successor message certificates :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  echo_ir_parent_chain config state (ir_message_sender message) ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted receiver_initial receiver_in sender_chain action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_chains_rooted.
  apply echo_ir_remove_preserves_parent_chains_rooted.
  eapply echo_ir_install_parent_preserves_parent_chains_rooted; eauto.
Qed.

Lemma echo_ir_leaf_parent_chains_rooted
    config state successor message certificates :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state (ir_message_receiver message) = None ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  echo_ir_parent_chain config state (ir_message_sender message) ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted receiver_initial receiver_in sender_chain action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_chains_rooted.
  apply echo_ir_remove_preserves_parent_chains_rooted.
  eapply echo_ir_install_parent_preserves_parent_chains_rooted; eauto.
Qed.

Lemma echo_ir_repeated_parent_chains_rooted
    config state successor message certificates :
  echo_ir_parent_chains_rooted config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_chains_rooted.
  now apply echo_ir_remove_preserves_parent_chains_rooted.
Qed.

Lemma echo_ir_root_request_parent_chains_rooted
    config state successor message certificates :
  echo_ir_parent_chains_rooted config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_parent_chains_rooted.
  now apply echo_ir_remove_preserves_parent_chains_rooted.
Qed.

Lemma echo_ir_participant_more_parent_chains_rooted
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_chains_rooted config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending)) in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    apply echo_ir_remove_preserves_parent_chains_rooted.
    eapply echo_ir_update_same_parent_preserves_parent_chains_rooted; eauto.
    unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_final_parent_chains_rooted
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_chains_rooted config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    change (echo_ir_parent_chains_rooted config
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_parent_chains_rooted.
    apply echo_ir_remove_preserves_parent_chains_rooted.
    eapply echo_ir_update_same_parent_preserves_parent_chains_rooted; eauto.
    unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_more_parent_chains_rooted
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state
    (echo_ir_config_initiator node config) = None ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted root_parent action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_parent_chains_rooted.
  eapply echo_ir_update_same_parent_preserves_parent_chains_rooted; eauto.
Qed.

Lemma echo_ir_initiator_final_parent_chains_rooted
    config state successor message
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_parent_chains_rooted config state ->
  echo_ir_parent_value node state
    (echo_ir_config_initiator node config) = None ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros rooted root_parent action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_parent_chains_rooted.
  eapply echo_ir_update_same_parent_preserves_parent_chains_rooted; eauto.
Qed.

Theorem EchoStep_preserves_parent_chains_rooted
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_initiator_parent_none node config state ->
  echo_ir_discovered_participants_parented node config state ->
  echo_ir_request_senders_discovered node state ->
  echo_ir_queued_edges_valid node config state ->
  echo_ir_parent_chains_rooted config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_parent_chains_rooted config successor.
Proof.
  intros root_parent parented request_senders queued_edges rooted step.
  assert (root_parent_value : echo_ir_parent_value node state
    (echo_ir_config_initiator node config) = None).
  { unfold echo_ir_initiator_parent_none in root_parent.
    unfold echo_ir_parent_value. now rewrite root_parent. }
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_parent_chains_rooted; eauto.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_first_nonleaf_enabled_parent_none node node_eq
        config state message certificates enabled) as receiver_initial.
      pose proof (echo_ir_resolved_delivery_queued node state
        external_event message certificates resolved) as queued.
      pose proof (echo_ir_enabled_request_pattern_kind node node_eq
        config state message certificates
        (@echo_ir_first_request_nonleaf_rule node) eq_refl enabled)
        as request_kind.
      destruct (queued_edges message queued) as
        [sender_in [receiver_in edge]].
      assert (sender_chain : echo_ir_parent_chain config state
        (ir_message_sender message)).
      { destruct (node_eq (ir_message_sender message)
          (echo_ir_config_initiator node config)) as [same_root | not_root].
        - rewrite same_root. constructor.
        - pose proof (request_senders message queued request_kind)
            as discovered.
          destruct (parented (ir_message_sender message) not_root discovered)
            as [parent parent_link].
          now apply rooted with (parent := parent). }
      eapply echo_ir_nonleaf_parent_chains_rooted; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_enabled_receiver_parent_none config state message
          certificates (@echo_ir_first_request_leaf_rule node) enabled
          ltac:(cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
            now right; left)) as receiver_initial.
        pose proof (echo_ir_resolved_delivery_queued node state
          external_event message certificates resolved) as queued.
        pose proof (echo_ir_enabled_request_pattern_kind node node_eq
          config state message certificates
          (@echo_ir_first_request_leaf_rule node) eq_refl enabled)
          as request_kind.
        destruct (queued_edges message queued) as
          [sender_in [receiver_in edge]].
        assert (sender_chain : echo_ir_parent_chain config state
          (ir_message_sender message)).
        { destruct (node_eq (ir_message_sender message)
            (echo_ir_config_initiator node config)) as [same_root | not_root].
          - rewrite same_root. constructor.
          - pose proof (request_senders message queued request_kind)
              as discovered.
            destruct (parented (ir_message_sender message) not_root discovered)
              as [parent parent_link].
            now apply rooted with (parent := parent). }
        eapply echo_ir_leaf_parent_chains_rooted; eauto.
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_repeated_parent_chains_rooted; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              eapply echo_ir_root_request_parent_chains_rooted; eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 pose proof (echo_ir_enabled_expected_parent node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)) as old_parent.
                 eapply echo_ir_participant_more_parent_chains_rooted; eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     pose proof (echo_ir_enabled_expected_parent node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)) as old_parent.
                     eapply echo_ir_participant_final_parent_chains_rooted;
                       eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         eapply echo_ir_initiator_more_parent_chains_rooted;
                           eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             eapply
                               echo_ir_initiator_final_parent_chains_rooted;
                               eauto.
                         *** contradiction.
Qed.

Definition echo_ir_rooted_pending_bundle config state : Prop :=
  echo_ir_reply_pending_bundle config state /\
  echo_ir_parent_chains_rooted config state.

Lemma EchoStep_preserves_rooted_pending_bundle
    config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_rooted_pending_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_rooted_pending_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric [pending_bundle rooted] step.
  assert (pending_after : echo_ir_reply_pending_bundle config successor).
  { eapply EchoStep_preserves_reply_pending_bundle; eauto. }
  split; [exact pending_after |].
  destruct pending_bundle as [child_bundle replies].
  destruct child_bundle as [request_pending children].
  destruct request_pending as [edge_bundle requests].
  destruct edge_bundle as [parent_bundle reply_unique].
  destruct parent_bundle as
    [request_bundle [root_parent [reply_discovery parent_replies]]].
  destruct request_bundle as
    [[parent_edges queued_edges]
      [discovered [accounting [reply_support reverse]]]].
  destruct reply_support as
    [parent_targets [request_senders reply_receivers]].
  eapply EchoStep_preserves_parent_chains_rooted; eauto.
Qed.

Lemma echo_ir_initial_rooted_pending_bundle config :
  echo_ir_rooted_pending_bundle config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_reply_pending_bundle.
  - apply echo_ir_initial_parent_chains_rooted.
Qed.

Theorem echo_ir_path_preserves_rooted_pending_bundle config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_rooted_pending_bundle config initial ->
  echo_ir_rooted_pending_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_rooted_pending_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_parent_chains_rooted config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_parent_chains_rooted config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_rooted_pending_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_rooted_pending_bundle config)) as bundle.
  exact (proj2 bundle).
Qed.

Lemma echo_ir_parent_chain_propagates_pending
    config state owner :
  echo_ir_completion_well_formed config state ->
  echo_ir_unfinished_children_pending config state ->
  echo_ir_parent_chain config state owner ->
  forall item,
    In item (echo_ir_pending_value node state owner) ->
    exists root_item,
      In root_item (echo_ir_pending_value node state
        (echo_ir_config_initiator node config)).
Proof.
  intros completion children chain.
  induction chain; intros item pending.
  - now exists item.
  - assert (unfinished : echo_ir_finished_value node state child = false).
    { destruct (echo_ir_finished_value node state child) eqn:finished;
        [|reflexivity].
      pose proof (completion child H finished) as empty.
      rewrite empty in pending. contradiction. }
    pose proof (children child parent H H0 unfinished) as parent_pending.
    now apply IHchain with (item := child).
Qed.

Theorem echo_ir_pending_obligation_reaches_initiator
    config state owner item :
  echo_ir_discovered_participants_parented node config state ->
  echo_ir_parent_chains_rooted config state ->
  echo_ir_completion_well_formed config state ->
  echo_ir_unfinished_children_pending config state ->
  In owner (ir_config_nodes config) ->
  In item (echo_ir_pending_value node state owner) ->
  exists root_item,
    In root_item (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)).
Proof.
  intros parented rooted completion children owner_in pending.
  assert (chain : echo_ir_parent_chain config state owner).
  { destruct (node_eq owner (echo_ir_config_initiator node config))
      as [root | nonroot].
    - subst owner. constructor.
    - assert (discovered : echo_ir_local_discovered node state owner).
      { right. left. intro empty. rewrite empty in pending. contradiction. }
      destruct (parented owner nonroot discovered) as [parent parent_link].
      now apply rooted with (parent := parent). }
  eapply echo_ir_parent_chain_propagates_pending; eauto.
Qed.

Theorem echo_reachable_pending_reaches_initiator
    config state owner item :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  In owner (ir_config_nodes config) ->
  In item (echo_ir_pending_value node state owner) ->
  exists root_item,
    In root_item (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)).
Proof.
  intros initiator_in neighbors_valid symmetric reachable owner_in pending.
  eapply echo_ir_pending_obligation_reaches_initiator.
  - eapply echo_reachable_discovered_participants_parented; eauto.
  - eapply echo_reachable_parent_chains_rooted; eauto.
  - now apply echo_reachable_completion.
  - eapply echo_reachable_unfinished_children_pending; eauto.
  - exact owner_in.
  - exact pending.
Qed.

Lemma echo_ir_parent_chain_no_self_parent
    config state owner :
  echo_ir_parent_value node state
    (echo_ir_config_initiator node config) = None ->
  echo_ir_parent_chain config state owner ->
  echo_ir_parent_value node state owner <> Some owner.
Proof.
  intros root_parent chain. induction chain; intro self_parent.
  - rewrite root_parent in self_parent. discriminate.
  - rewrite H0 in self_parent. injection self_parent as <-.
    now apply IHchain.
Qed.

Lemma echo_ir_parent_chain_no_mutual_parent
    config state owner :
  echo_ir_parent_value node state
    (echo_ir_config_initiator node config) = None ->
  echo_ir_parent_chain config state owner ->
  forall parent,
    echo_ir_parent_value node state owner = Some parent ->
    echo_ir_parent_value node state parent <> Some owner.
Proof.
  intros root_parent chain. induction chain; intros observed parent_link back.
  - rewrite root_parent in parent_link. discriminate.
  - rewrite H0 in parent_link. injection parent_link as <-.
    specialize (IHchain child back).
    now apply IHchain.
Qed.

Theorem echo_reachable_no_self_parent config state owner :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  In owner (ir_config_nodes config) ->
  echo_ir_parent_value node state owner <> Some owner.
Proof.
  intros initiator_in neighbors_valid symmetric reachable owner_in.
  pose proof (echo_reachable_parent_chains_rooted config state
    initiator_in neighbors_valid symmetric reachable) as rooted.
  pose proof (echo_reachable_initiator_parent_none node node_eq config state
    reachable) as root_parent.
  unfold echo_ir_initiator_parent_none in root_parent.
  destruct (echo_ir_parent_value node state owner) eqn:parent_value.
  - intro self_parent.
    apply (echo_ir_parent_chain_no_self_parent config state owner
      (ltac:(unfold echo_ir_parent_value; now rewrite root_parent))
      (ltac:(now apply rooted with (parent := n)))).
    now rewrite parent_value.
  - discriminate.
Qed.

Theorem echo_reachable_no_mutual_parent
    config state left right :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  In left (ir_config_nodes config) ->
  echo_ir_parent_value node state left = Some right ->
  echo_ir_parent_value node state right <> Some left.
Proof.
  intros initiator_in neighbors_valid symmetric reachable left_in left_parent.
  pose proof (echo_reachable_parent_chains_rooted config state
    initiator_in neighbors_valid symmetric reachable) as rooted.
  pose proof (echo_reachable_initiator_parent_none node node_eq config state
    reachable) as root_parent.
  unfold echo_ir_initiator_parent_none in root_parent.
  eapply echo_ir_parent_chain_no_mutual_parent.
  - unfold echo_ir_parent_value. now rewrite root_parent.
  - now apply rooted with (parent := right).
  - exact left_parent.
Qed.

End EchoIRExecutableObligations.
