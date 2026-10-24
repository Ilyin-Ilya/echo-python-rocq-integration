(** * Direct reverse request/reply exclusion for generic Echo IR *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery EchoIRExecutableTopology
  EchoIRExecutableRequestAccounting EchoIRExecutableRequestParent
  EchoIRExecutableReplyDiscovery.

Section EchoIRExecutableRequestReply.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_request_reply_reverse_distinct
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall request reply,
    In request (ir_message_store state) ->
    In reply (ir_message_store state) ->
    ir_message_kind request = EchoIRRequest ->
    ir_message_kind reply = EchoIRReply ->
    ir_message_sender request = ir_message_receiver reply ->
    ir_message_receiver request = ir_message_sender reply ->
    False.

Lemma echo_ir_remove_preserves_request_reply_reverse_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_reply_reverse_distinct
    (ir_remove_selected_message state selected_id).
Proof.
  intros invariant request reply request_in reply_in
    request_kind reply_kind reverse_sender reverse_receiver.
  eapply invariant.
  - cbn [ir_remove_selected_message ir_message_store] in request_in.
    now apply (echo_ir_remove_message_in node selected_id _ request).
  - cbn [ir_remove_selected_message ir_message_store] in reply_in.
    now apply (echo_ir_remove_message_in node selected_id _ reply).
  - exact request_kind.
  - exact reply_kind.
  - exact reverse_sender.
  - exact reverse_receiver.
Qed.

Lemma echo_ir_remove_emit_requests_preserves_reverse_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_reply_receivers_discovered node state ->
  ~ echo_ir_local_discovered node state sender ->
  echo_ir_request_reply_reverse_distinct
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id selected))
      EchoIRRequest sender receivers payload).
Proof.
  intros invariant replies sender_initial request reply
    request_in reply_in request_kind reply_kind
    reverse_sender reverse_receiver.
  cbn [ir_emit_messages ir_message_store] in request_in, reply_in.
  apply in_app_or in request_in.
  apply in_app_or in reply_in.
  destruct request_in as [old_request | new_request];
    destruct reply_in as [old_reply | new_reply].
  - eapply invariant.
    + cbn [ir_remove_selected_message ir_message_store] in old_request.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ request).
    + cbn [ir_remove_selected_message ir_message_store] in old_reply.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ reply).
    + exact request_kind.
    + exact reply_kind.
    + exact reverse_sender.
    + exact reverse_receiver.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRRequest sender receivers payload reply new_reply) as emitted_kind.
    rewrite reply_kind in emitted_kind. discriminate.
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRRequest sender receivers payload request new_request)
      as [new_sender receiver_in].
    apply sender_initial.
    rewrite <- new_sender, reverse_sender.
    apply replies with (message := reply).
    + cbn [ir_remove_selected_message ir_message_store] in old_reply.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ reply).
    + exact reply_kind.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRRequest sender receivers payload reply new_reply) as emitted_kind.
    rewrite reply_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_remove_emit_reverse_reply_preserves_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_edges_unique node state ->
  echo_ir_message_ids_well_formed node state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRRequest ->
  echo_ir_request_reply_reverse_distinct
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id selected))
      EchoIRReply (ir_message_receiver selected)
      [ir_message_sender selected] []).
Proof.
  intros invariant unique [_ ids_nodup] selected_in selected_kind
    request reply request_in reply_in request_kind reply_kind
    reverse_sender reverse_receiver.
  cbn [ir_emit_messages ir_message_store] in request_in, reply_in.
  apply in_app_or in request_in.
  apply in_app_or in reply_in.
  destruct request_in as [old_request | new_request];
    destruct reply_in as [old_reply | new_reply].
  - eapply invariant.
    + cbn [ir_remove_selected_message ir_message_store] in old_request.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ request).
    + cbn [ir_remove_selected_message ir_message_store] in old_reply.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ reply).
    + exact request_kind.
    + exact reply_kind.
    + exact reverse_sender.
    + exact reverse_receiver.
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRReply (ir_message_receiver selected)
      [ir_message_sender selected] [] reply new_reply)
      as [reply_sender reply_receiver_in].
    destruct reply_receiver_in as [reply_receiver | impossible];
      [| contradiction].
    assert (same_request : request = selected).
    {
      eapply unique.
      - cbn [ir_remove_selected_message ir_message_store] in old_request.
        now apply (echo_ir_remove_message_in node
          (ir_message_id selected) _ request).
      - exact selected_in.
      - exact request_kind.
      - exact selected_kind.
      - rewrite reverse_sender, reply_receiver. reflexivity.
      - rewrite reverse_receiver, reply_sender. reflexivity.
    }
    subst request.
    cbn [ir_remove_selected_message ir_message_store] in old_request.
    exact (echo_ir_remove_message_selected_not_in node selected
      (ir_message_store state) ids_nodup old_request).
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRReply (ir_message_receiver selected)
      [ir_message_sender selected] [] request new_request) as emitted_kind.
    rewrite request_kind in emitted_kind. discriminate.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRReply (ir_message_receiver selected)
      [ir_message_sender selected] [] request new_request) as emitted_kind.
    rewrite request_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_remove_emit_parent_reply_preserves_reverse_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (parent : node) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_parent_distinct node state ->
  echo_ir_parent_value node state (ir_message_receiver selected) =
    Some parent ->
  echo_ir_request_reply_reverse_distinct
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id selected))
      EchoIRReply (ir_message_receiver selected) [parent] []).
Proof.
  intros invariant parent_distinct installed request reply
    request_in reply_in request_kind reply_kind
    reverse_sender reverse_receiver.
  cbn [ir_emit_messages ir_message_store] in request_in, reply_in.
  apply in_app_or in request_in.
  apply in_app_or in reply_in.
  destruct request_in as [old_request | new_request];
    destruct reply_in as [old_reply | new_reply].
  - eapply invariant.
    + cbn [ir_remove_selected_message ir_message_store] in old_request.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ request).
    + cbn [ir_remove_selected_message ir_message_store] in old_reply.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ reply).
    + exact request_kind.
    + exact reply_kind.
    + exact reverse_sender.
    + exact reverse_receiver.
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRReply (ir_message_receiver selected) [parent] [] reply new_reply)
      as [reply_sender reply_receiver_in].
    destruct reply_receiver_in as [reply_receiver | impossible];
      [| contradiction].
    apply (parent_distinct request).
    + cbn [ir_remove_selected_message ir_message_store] in old_request.
      now apply (echo_ir_remove_message_in node
        (ir_message_id selected) _ request).
    + exact request_kind.
    + rewrite reverse_receiver, reply_sender.
      rewrite reverse_sender, <- reply_receiver.
      exact installed.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRReply (ir_message_receiver selected) [parent] []
      request new_request) as emitted_kind.
    rewrite request_kind in emitted_kind. discriminate.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_remove_selected_message state (ir_message_id selected)))
      EchoIRReply (ir_message_receiver selected) [parent] []
      request new_request) as emitted_kind.
    rewrite request_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_start_action_establishes_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros store_empty action.
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
  intros request reply request_in reply_in request_kind reply_kind.
  cbn [ir_emit_messages ir_message_store] in reply_in.
  apply in_app_or in reply_in as [old_reply | new_reply].
  - change (In reply (ir_message_store state)) in old_reply.
    rewrite store_empty in old_reply. contradiction.
  - pose proof (echo_ir_materialized_message_kind node
      (ir_next_message_id
        (ir_set_global_field
          (echo_ir_update_process node node_eq state
            (echo_ir_config_initiator node config) (IROptionNodeValue None)
            (IRListNodeValue
              (ir_config_neighbors config
                (echo_ir_config_initiator node config)))
            false) EchoIRStarted (IRBoolValue true)))
      EchoIRRequest (echo_ir_config_initiator node config)
      (ir_config_neighbors config
        (echo_ir_config_initiator node config)) []
      reply new_reply) as emitted_kind.
    rewrite reply_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_reply_receivers_discovered node state ->
  ~ echo_ir_local_discovered node state (ir_message_receiver message) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant replies receiver_initial action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  change (echo_ir_request_reply_reverse_distinct
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      EchoIRRequest (ir_message_receiver message)
      (ir_remove_node node_eq (ir_message_sender message)
        (ir_config_neighbors config (ir_message_receiver message))) [])).
  now apply echo_ir_remove_emit_requests_preserves_reverse_distinct.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_edges_unique node state ->
  echo_ir_message_ids_well_formed node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant unique ids queued request_kind action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  change (echo_ir_request_reply_reverse_distinct
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      EchoIRReply (ir_message_receiver message)
      [ir_message_sender message] [])).
  now apply echo_ir_remove_emit_reverse_reply_preserves_distinct.
Qed.

Lemma echo_ir_repeated_request_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_edges_unique node state ->
  echo_ir_message_ids_well_formed node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant unique ids queued request_kind action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  now apply echo_ir_remove_emit_reverse_reply_preserves_distinct.
Qed.

Lemma echo_ir_initiator_request_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_edges_unique node state ->
  echo_ir_message_ids_well_formed node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  ir_message_receiver message = echo_ir_config_initiator node config ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant unique ids queued request_kind receiver_root action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  unfold echo_ir_config_initiator in receiver_root.
  rewrite <- receiver_root.
  now apply echo_ir_remove_emit_reverse_reply_preserves_distinct.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant action. unfold echo_ir_participant_reply_more_rule in action.
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
      (ir_processes state (ir_message_receiver message) EchoIRPending))
      in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    change (echo_ir_request_reply_reverse_distinct
      (ir_remove_selected_message state (ir_message_id message))).
    now apply echo_ir_remove_preserves_request_reply_reverse_distinct.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  echo_ir_request_parent_distinct node state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant parent_distinct action.
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
    change (echo_ir_request_reply_reverse_distinct
      (ir_emit_messages
        (ir_remove_selected_message state (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_remove_emit_parent_reply_preserves_reverse_distinct.
    + exact invariant.
    + exact parent_distinct.
    + unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant action. unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  change (echo_ir_request_reply_reverse_distinct
    (ir_remove_selected_message state (ir_message_id message))).
  now apply echo_ir_remove_preserves_request_reply_reverse_distinct.
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_reply_reverse_distinct state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros invariant action. unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  change (echo_ir_request_reply_reverse_distinct
    (ir_remove_selected_message state (ir_message_id message))).
  now apply echo_ir_remove_preserves_request_reply_reverse_distinct.
Qed.

Theorem EchoStep_preserves_request_reply_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_discovered_participants_parented node config state ->
  echo_ir_request_parent_accounting node config state ->
  echo_ir_reply_discovery_support node config state ->
  echo_ir_request_reply_reverse_distinct state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_request_reply_reverse_distinct successor.
Proof.
  intros discovered_parented accounting reply_support invariant step.
  destruct accounting as [request_accounting [ids [sources parent_distinct]]].
  destruct request_accounting as [request_unique request_provenance].
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected
        [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in].
  - subst selected_rule.
    pose proof (eval_ir_rule_enabled_pattern node_eq config state
      runtime_event (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_action_establishes_reverse_distinct.
    + exact (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in].
    + subst selected_rule.
      pose proof (eval_ir_rule_enabled_pattern node_eq config state
        runtime_event (@echo_ir_first_request_nonleaf_rule node) enabled)
        as pattern.
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
      {
        intro receiver_discovered.
        destruct (discovered_parented (ir_message_receiver message)
          receiver_not_root receiver_discovered) as [parent installed].
        rewrite receiver_parent_none in installed. discriminate.
      }
      eapply echo_ir_first_request_nonleaf_action_preserves_reverse_distinct.
      * exact invariant.
      * exact (proj2 (proj2 reply_support)).
      * exact receiver_initial.
      * exact action.
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_resolved_delivery_queued node
          state external_event message certificates resolved) as queued.
        pose proof (echo_ir_enabled_request_pattern_kind node node_eq
          config state message certificates
          (@echo_ir_first_request_leaf_rule node) eq_refl enabled)
          as request_kind.
        eapply echo_ir_first_request_leaf_action_preserves_reverse_distinct;
          eauto.
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           pose proof (echo_ir_resolved_delivery_queued node
             state external_event message certificates resolved) as queued.
           pose proof (echo_ir_enabled_request_pattern_kind node node_eq
             config state message certificates
             (@echo_ir_repeated_request_rule node) eq_refl enabled)
             as request_kind.
           eapply echo_ir_repeated_request_action_preserves_reverse_distinct;
             eauto.
        -- destruct selected_in as [same | selected_in].
           ++ subst selected_rule.
              pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              pose proof (echo_ir_resolved_delivery_queued node
                state external_event message certificates resolved) as queued.
              pose proof (echo_ir_enabled_request_pattern_kind node node_eq
                config state message certificates
                (@echo_ir_initiator_request_rule node) eq_refl enabled)
                as request_kind.
              pose proof (echo_ir_enabled_initiator_receiver node node_eq
                config state message certificates
                (@echo_ir_initiator_request_rule node) enabled
                ltac:(cbn [echo_ir_initiator_request_rule]; now left))
                as receiver_root.
              eapply
                echo_ir_initiator_request_action_preserves_reverse_distinct;
                eauto.
           ++ destruct selected_in as [same | selected_in].
              ** subst selected_rule.
                 pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event
                   (@echo_ir_participant_reply_more_rule node) enabled)
                   as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 now apply
                   echo_ir_participant_reply_more_action_preserves_reverse_distinct
                     with (config := config) (state := state)
                       (message := message) (certificates := certificates).
              ** destruct selected_in as [same | selected_in].
                 --- subst selected_rule.
                     pose proof (eval_ir_rule_enabled_pattern
                       node_eq config state runtime_event
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
                     eapply
                       echo_ir_participant_reply_final_action_preserves_reverse_distinct;
                       eauto.
                 --- destruct selected_in as [same | selected_in].
                     +++ subst selected_rule.
                         pose proof (eval_ir_rule_enabled_pattern
                           node_eq config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         now apply
                           echo_ir_initiator_reply_more_action_preserves_reverse_distinct
                             with (config := config) (state := state)
                               (message := message)
                               (certificates := certificates).
                     +++ destruct selected_in as [same | selected_in].
                         *** subst selected_rule.
                             pose proof (eval_ir_rule_enabled_pattern
                               node_eq config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             now apply
                               echo_ir_initiator_reply_final_action_preserves_reverse_distinct
                                 with (config := config) (state := state)
                                   (message := message)
                                   (certificates := certificates).
                         *** contradiction.
Qed.

Definition echo_ir_request_reply_bundle
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_topology_well_formed node config state /\
  echo_ir_discovered_participants_parented node config state /\
  echo_ir_request_parent_accounting node config state /\
  echo_ir_reply_discovery_support node config state /\
  echo_ir_request_reply_reverse_distinct state.

Lemma EchoStep_preserves_request_reply_bundle
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_request_reply_bundle config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_request_reply_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric
    [topology [discovered [accounting [reply_support reverse]]]] step.
  assert (topology_after :
    echo_ir_topology_well_formed node config successor).
  {
    eapply EchoStep_preserves_topology_well_formed.
    - exact initiator_in.
    - exact neighbors_valid.
    - exact symmetric.
    - exact topology.
    - exact step.
  }
  assert (discovered_after :
    echo_ir_discovered_participants_parented node config successor).
  {
    eapply EchoStep_preserves_discovered_participants_parented.
    - exact discovered.
    - exact step.
  }
  assert (accounting_after :
    echo_ir_request_parent_accounting node config successor).
  {
    eapply EchoStep_preserves_request_parent_accounting.
    - exact initiator_in.
    - exact neighbors_valid.
    - exact topology.
    - exact accounting.
    - exact step.
  }
  assert (reply_support_after :
    echo_ir_reply_discovery_support node config successor).
  {
    eapply EchoStep_preserves_reply_discovery_support.
    - exact topology.
    - exact reply_support.
    - exact step.
  }
  assert (reverse_after :
    echo_ir_request_reply_reverse_distinct successor).
  {
    eapply EchoStep_preserves_request_reply_reverse_distinct.
    - exact discovered.
    - exact accounting.
    - exact reply_support.
    - exact reverse.
    - exact step.
  }
  split; [exact topology_after |].
  split; [exact discovered_after |].
  split; [exact accounting_after |].
  split; assumption.
Qed.

Lemma echo_ir_initial_request_reply_reverse_distinct :
  echo_ir_request_reply_reverse_distinct (@echo_initial_state node).
Proof.
  intros request reply request_in. contradiction.
Qed.

Lemma echo_ir_initial_request_reply_bundle
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_request_reply_bundle config (@echo_initial_state node).
Proof.
  split; [apply echo_ir_initial_topology_well_formed |].
  split; [apply echo_ir_initial_discovered_participants_parented |].
  split; [apply echo_ir_initial_request_parent_accounting |].
  split.
  - apply echo_ir_initial_reply_discovery_support.
  - apply echo_ir_initial_request_reply_reverse_distinct.
Qed.

Theorem echo_ir_path_preserves_request_reply_bundle
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_request_reply_bundle config initial ->
  echo_ir_request_reply_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_request_reply_bundle.
    + exact initiator_in.
    + exact neighbors_valid.
    + exact symmetric.
    + exact bundle.
    + exists rule. exact H.
Qed.

Theorem echo_reachable_request_reply_bundle
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_request_reply_bundle config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  eapply echo_ir_path_preserves_request_reply_bundle.
  - exact initiator_in.
  - exact neighbors_valid.
  - exact symmetric.
  - exact reachable.
  - apply echo_ir_initial_request_reply_bundle.
Qed.

Corollary echo_reachable_request_reply_reverse_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_request_reply_reverse_distinct state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  exact (proj2 (proj2 (proj2 (proj2
    (echo_reachable_request_reply_bundle config state
      initiator_in neighbors_valid symmetric reachable))))).
Qed.

End EchoIRExecutableRequestReply.
