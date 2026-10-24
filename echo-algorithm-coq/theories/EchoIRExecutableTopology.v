(** * Direct topology invariants for the public Echo IR executable

    Parent pointers and queued messages are checked against the generic
    configuration's node and neighbor views.  The proof uses only the generic
    interpreter and generated Echo rules, with no legacy transition or
    simulation dependency. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery.

Section EchoIRExecutableTopology.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_config_neighbors_symmetric
    (config : ir_protocol_config node echo_ir_signature) : Prop :=
  forall left right,
    In left (ir_config_nodes config) ->
    In right (ir_config_neighbors config left) ->
    In left (ir_config_neighbors config right).

Definition echo_ir_parent_edges_valid
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall child parent,
    In child (ir_config_nodes config) ->
    echo_ir_parent_value node state child = Some parent ->
    In parent (ir_config_nodes config) /\
    In parent (ir_config_neighbors config child).

Definition echo_ir_message_edge_valid
    (config : ir_protocol_config node echo_ir_signature)
    (message : ir_message node echo_ir_signature) : Prop :=
  In (ir_message_sender message) (ir_config_nodes config) /\
  In (ir_message_receiver message) (ir_config_nodes config) /\
  In (ir_message_receiver message)
    (ir_config_neighbors config (ir_message_sender message)).

Definition echo_ir_queued_edges_valid
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    echo_ir_message_edge_valid config message.

Definition echo_ir_topology_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_parent_edges_valid config state /\
  echo_ir_queued_edges_valid config state.

Lemma echo_ir_remove_message_in
    (selected_id : nat)
    (messages : list (ir_message node echo_ir_signature))
    (candidate : ir_message node echo_ir_signature) :
  In candidate (ir_remove_message selected_id messages) ->
  In candidate messages.
Proof.
  induction messages as [|head rest IH]; cbn; intro member.
  - contradiction.
  - destruct (Nat.eqb selected_id (ir_message_id head)).
    + now right.
    + destruct member as [same | member].
      * now left.
      * right. now apply IH.
Qed.

Lemma echo_ir_materialized_message_fields
    (next_id : nat)
    (kind : echo_ir_message_kind)
    (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature)
    (message : ir_message node echo_ir_signature) :
  In message
    (@ir_materialize_messages node echo_ir_signature
      next_id kind sender receivers payload) ->
  ir_message_sender message = sender /\
  In (ir_message_receiver message) receivers.
Proof.
  revert next_id.
  induction receivers as [|receiver rest IH]; intros next_id member.
  - contradiction.
  - cbn [ir_materialize_messages] in member.
    destruct member as [same | member].
    + subst message. cbn. auto.
    + destruct (IH (S next_id) member) as [same_sender receiver_in].
      split; [exact same_sender | now right].
Qed.

Lemma echo_ir_parent_edges_processes
    (config : ir_protocol_config node echo_ir_signature)
    (left right : ir_protocol_state node echo_ir_signature) :
  echo_ir_parent_edges_valid config left ->
  ir_processes right = ir_processes left ->
  echo_ir_parent_edges_valid config right.
Proof.
  intros valid processes child parent child_in parent_value.
  unfold echo_ir_parent_value in parent_value.
  rewrite processes in parent_value.
  now apply (valid child parent child_in).
Qed.

Lemma echo_ir_queued_edges_store
    (config : ir_protocol_config node echo_ir_signature)
    (left right : ir_protocol_state node echo_ir_signature) :
  echo_ir_queued_edges_valid config left ->
  ir_message_store right = ir_message_store left ->
  echo_ir_queued_edges_valid config right.
Proof.
  intros valid store message queued.
  rewrite store in queued.
  now apply valid.
Qed.

Lemma echo_ir_remove_selected_preserves_queued_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_queued_edges_valid config state ->
  echo_ir_queued_edges_valid config
    (ir_remove_selected_message state selected_id).
Proof.
  intros valid message queued.
  cbn [ir_remove_selected_message ir_message_store] in queued.
  apply valid.
  now apply (echo_ir_remove_message_in selected_id _ message).
Qed.

Lemma echo_ir_emit_preserves_queued_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  echo_ir_queued_edges_valid config state ->
  In sender (ir_config_nodes config) ->
  (forall receiver,
    In receiver receivers ->
    In receiver (ir_config_nodes config) /\
    In receiver (ir_config_neighbors config sender)) ->
  echo_ir_queued_edges_valid config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros old_valid sender_in receivers_valid message queued.
  cbn [ir_emit_messages ir_message_store] in queued.
  apply in_app_or in queued as [old | emitted].
  - now apply old_valid.
  - destruct (echo_ir_materialized_message_fields
      (ir_next_message_id state) kind sender receivers payload message emitted)
      as [same_sender receiver_in].
    specialize (receivers_valid (ir_message_receiver message) receiver_in).
    destruct receivers_valid as [receiver_configured receiver_neighbor].
    unfold echo_ir_message_edge_valid.
    rewrite same_sender. auto.
Qed.

Lemma echo_ir_update_process_none_preserves_parent_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node)
    (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_parent_edges_valid config state ->
  echo_ir_parent_edges_valid config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue None) pending finished).
Proof.
  intros invariant child parent child_in parent_value.
  unfold echo_ir_parent_value, echo_ir_update_process in parent_value.
  destruct (node_eq owner child) as [same | different].
  - subst child.
    rewrite ir_set_local_field_read_different in parent_value
      by discriminate.
    rewrite ir_set_local_field_read_different in parent_value
      by discriminate.
    rewrite ir_set_local_field_same in parent_value.
    discriminate.
  - repeat rewrite ir_set_local_field_read_other_process
      in parent_value by exact different.
    now apply (invariant child parent child_in).
Qed.

Lemma echo_ir_update_process_some_preserves_parent_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node)
    (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_parent_edges_valid config state ->
  (In owner (ir_config_nodes config) ->
    In parent (ir_config_nodes config) /\
    In parent (ir_config_neighbors config owner)) ->
  echo_ir_parent_edges_valid config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished).
Proof.
  intros invariant parent_valid child installed child_in parent_value.
  unfold echo_ir_parent_value, echo_ir_update_process in parent_value.
  destruct (node_eq owner child) as [same | different].
  - subst child.
    rewrite ir_set_local_field_read_different in parent_value
      by discriminate.
    rewrite ir_set_local_field_read_different in parent_value
      by discriminate.
    rewrite ir_set_local_field_same in parent_value.
    inversion parent_value. subst installed.
    now apply parent_valid.
  - repeat rewrite ir_set_local_field_read_other_process
      in parent_value by exact different.
    now apply (invariant child installed child_in).
Qed.

Lemma echo_ir_resolved_delivery_queued
    (state : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  ir_resolve_event state external_event =
    Some (IRRuntimeDeliver message certificates) ->
  In message (ir_message_store state).
Proof.
  destruct external_event as [start_certificates|selected_id supplied];
    intro resolved; cbn [ir_resolve_event] in resolved;
    try discriminate.
  destruct (resolved_delivery_was_queued
    state selected_id supplied (IRRuntimeDeliver message certificates)
    resolved) as [selected [queued [same_id event_shape]]].
  inversion event_shape. subst selected. exact queued.
Qed.

Lemma echo_ir_update_process_preserves_queued_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_queued_edges_valid config state ->
  echo_ir_queued_edges_valid config
    (echo_ir_update_process node node_eq state owner
      parent pending finished).
Proof.
  intro valid. eapply echo_ir_queued_edges_store.
  - exact valid.
  - reflexivity.
Qed.

Lemma echo_ir_set_global_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (value : ir_value node IRBool) :
  echo_ir_topology_well_formed config state ->
  echo_ir_topology_well_formed config
    (ir_set_global_field state EchoIRStarted value).
Proof.
  intros [parents queued]. split.
  - eapply echo_ir_parent_edges_processes; [exact parents | reflexivity].
  - eapply echo_ir_queued_edges_store; [exact queued | reflexivity].
Qed.

Lemma echo_ir_remove_selected_preserves_parent_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_parent_edges_valid config state ->
  echo_ir_parent_edges_valid config
    (ir_remove_selected_message state selected_id).
Proof.
  intro valid. eapply echo_ir_parent_edges_processes.
  - exact valid.
  - reflexivity.
Qed.

Lemma echo_ir_emit_preserves_parent_edges
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  echo_ir_parent_edges_valid config state ->
  echo_ir_parent_edges_valid config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intro valid. eapply echo_ir_parent_edges_processes.
  - exact valid.
  - reflexivity.
Qed.

Lemma echo_ir_reverse_message_edge_valid
    (config : ir_protocol_config node echo_ir_signature)
    (message : ir_message node echo_ir_signature) :
  echo_ir_config_neighbors_symmetric config ->
  echo_ir_message_edge_valid config message ->
  In (ir_message_sender message) (ir_config_nodes config) /\
  In (ir_message_sender message)
    (ir_config_neighbors config (ir_message_receiver message)).
Proof.
  intros symmetric [sender_in [receiver_in edge]]. split.
  - exact sender_in.
  - now apply symmetric.
Qed.

Lemma echo_ir_start_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  (forall receiver,
    In receiver
      (ir_config_neighbors config (echo_ir_config_initiator node config)) ->
    In receiver (ir_config_nodes config) /\
    In receiver (ir_config_neighbors config
      (echo_ir_config_initiator node config))) ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology initiator_in order_valid action.
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
  change (echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_set_global_field
        (echo_ir_update_process node node_eq state
          (echo_ir_config_initiator node config)
          (IROptionNodeValue None)
          (IRListNodeValue (ir_config_neighbors config initiator))
          false)
        EchoIRStarted (IRBoolValue true))
      EchoIRRequest (echo_ir_config_initiator node config)
      (ir_config_neighbors config initiator) [])).
  assert (updated : echo_ir_topology_well_formed config
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None)
      (IRListNodeValue (ir_config_neighbors config initiator))
      false)).
  {
    destruct topology as [parents queued]. split.
    - now apply echo_ir_update_process_none_preserves_parent_edges.
    - now apply echo_ir_update_process_preserves_queued_edges.
  }
  pose proof (echo_ir_set_global_preserves_topology config _
    (IRBoolValue true) updated) as after_global.
  destruct after_global as [parents queued]. split.
  - now apply echo_ir_emit_preserves_parent_edges.
  - eapply echo_ir_emit_preserves_queued_edges.
    + exact queued.
    + exact initiator_in.
    + exact order_valid.
Qed.

Lemma echo_ir_updated_delivery_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (owner : node)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_topology_well_formed config state ->
  echo_ir_parent_edges_valid config
    (echo_ir_update_process node node_eq state
      owner parent pending finished) ->
  echo_ir_topology_well_formed config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        owner parent pending finished)
      (ir_message_id message)).
Proof.
  intros [_ queued] updated_parents. split.
  - now apply echo_ir_remove_selected_preserves_parent_edges.
  - apply echo_ir_remove_selected_preserves_queued_edges.
    now apply echo_ir_update_process_preserves_queued_edges.
Qed.

Lemma echo_ir_emit_after_delivery_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode)
    (finished : bool)
    (kind : echo_ir_message_kind)
    (receivers : list node) :
  echo_ir_topology_well_formed config state ->
  echo_ir_parent_edges_valid config
    (echo_ir_update_process node node_eq state
      (ir_message_receiver message) parent pending finished) ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  (forall receiver,
    In receiver receivers ->
    In receiver (ir_config_nodes config) /\
    In receiver
      (ir_config_neighbors config (ir_message_receiver message))) ->
  echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message) parent pending finished)
        (ir_message_id message))
      kind (ir_message_receiver message) receivers []).
Proof.
  intros topology parents receiver_in receivers_valid.
  pose proof (echo_ir_updated_delivery_preserves_topology
    config state message (ir_message_receiver message)
    parent pending finished topology parents)
    as removed.
  destruct removed as [removed_parents removed_queued]. split.
  - now apply echo_ir_emit_preserves_parent_edges.
  - eapply echo_ir_emit_preserves_queued_edges.
    + exact removed_queued.
    + exact receiver_in.
    + exact receivers_valid.
Qed.

Lemma echo_ir_emit_after_message_only_delivery_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (kind : echo_ir_message_kind)
    (receivers : list node) :
  echo_ir_topology_well_formed config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  (forall receiver,
    In receiver receivers ->
    In receiver (ir_config_nodes config) /\
    In receiver
      (ir_config_neighbors config (ir_message_receiver message))) ->
  echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      kind (ir_message_receiver message) receivers []).
Proof.
  intros [parents queued] receiver_in receivers_valid.
  assert (removed : echo_ir_topology_well_formed config
    (ir_remove_selected_message state (ir_message_id message))).
  {
    split.
    - now apply echo_ir_remove_selected_preserves_parent_edges.
    - now apply echo_ir_remove_selected_preserves_queued_edges.
  }
  destruct removed as [removed_parents removed_queued]. split.
  - now apply echo_ir_emit_preserves_parent_edges.
  - eapply echo_ir_emit_preserves_queued_edges.
    + exact removed_queued.
    + exact receiver_in.
    + exact receivers_valid.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  (In (ir_message_receiver message) (ir_config_nodes config) ->
    In (ir_message_sender message) (ir_config_nodes config) /\
    In (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message))) ->
  (forall receiver,
    In receiver
      (ir_remove_node node_eq (ir_message_sender message)
        (ir_config_neighbors config (ir_message_receiver message))) ->
    In receiver (ir_config_nodes config) /\
    In receiver
      (ir_config_neighbors config (ir_message_receiver message))) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology receiver_in parent_valid forwards_valid action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors, echo_ir_emit_many,
    echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  change (echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some (ir_message_sender message)))
          (IRListNodeValue
            (ir_remove_node node_eq (ir_message_sender message)
              (ir_config_neighbors config (ir_message_receiver message))))
          false)
        (ir_message_id message))
      EchoIRRequest (ir_message_receiver message)
      (ir_remove_node node_eq (ir_message_sender message)
        (ir_config_neighbors config (ir_message_receiver message))) [])).
  eapply echo_ir_emit_after_delivery_preserves_topology.
  - exact topology.
  - apply echo_ir_update_process_some_preserves_parent_edges.
    + exact (proj1 topology).
    + exact parent_valid.
  - exact receiver_in.
  - exact forwards_valid.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  (In (ir_message_receiver message) (ir_config_nodes config) ->
    In (ir_message_sender message) (ir_config_nodes config) /\
    In (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message))) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology receiver_in parent_valid action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  change (echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some (ir_message_sender message)))
          (IRListNodeValue []) true)
        (ir_message_id message))
      EchoIRReply (ir_message_receiver message)
      [ir_message_sender message] [])).
  eapply echo_ir_emit_after_delivery_preserves_topology.
  - exact topology.
  - apply echo_ir_update_process_some_preserves_parent_edges.
    + exact (proj1 topology).
    + exact parent_valid.
  - exact receiver_in.
  - intros receiver [same | impossible]; [subst receiver | contradiction].
    exact (parent_valid receiver_in).
Qed.

Lemma echo_ir_message_reply_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  ir_rule_action rule =
    echo_ir_sequence node
      [IRRemoveSelectedMessageAction;
       echo_ir_emit_one node EchoIRReply
         (echo_ir_receiver node) (echo_ir_sender node)] ->
  echo_ir_topology_well_formed config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  In (ir_message_sender message) (ir_config_nodes config) /\
  In (ir_message_sender message)
    (ir_config_neighbors config (ir_message_receiver message)) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates) (ir_rule_action rule) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros rule_action topology receiver_in reverse_valid action.
  rewrite rule_action in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  change (echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      EchoIRReply (ir_message_receiver message)
      [ir_message_sender message] [])).
  eapply echo_ir_emit_after_message_only_delivery_preserves_topology.
  - exact topology.
  - exact receiver_in.
  - intros receiver [same | impossible]; [subst receiver | contradiction].
    exact reverse_valid.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  (In (ir_message_receiver message) (ir_config_nodes config) ->
    In (echo_ir_parent_witness node state (ir_message_receiver message))
      (ir_config_nodes config) /\
    In (echo_ir_parent_witness node state (ir_message_receiver message))
      (ir_config_neighbors config (ir_message_receiver message))) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology parent_valid action.
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
      (ir_processes state (ir_message_receiver message) EchoIRPending))
      in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    change (echo_ir_topology_well_formed config
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some parent_node))
          (IRListNodeValue
            (ir_remove_node node_eq (ir_message_sender message)
              (ir_list_node_value_contents
                (ir_processes state
                  (ir_message_receiver message) EchoIRPending))))
          false)
        (ir_message_id message))).
    eapply echo_ir_updated_delivery_preserves_topology.
    + exact topology.
    + apply echo_ir_update_process_some_preserves_parent_edges.
      * exact (proj1 topology).
      * unfold echo_ir_parent_witness, echo_ir_parent_value in parent_valid.
        rewrite parent_value in parent_valid. exact parent_valid.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  (In (ir_message_receiver message) (ir_config_nodes config) ->
    In (echo_ir_parent_witness node state (ir_message_receiver message))
      (ir_config_nodes config) /\
    In (echo_ir_parent_witness node state (ir_message_receiver message))
      (ir_config_neighbors config (ir_message_receiver message))) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology receiver_in parent_valid action.
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
    change (echo_ir_topology_well_formed config
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    eapply echo_ir_emit_after_delivery_preserves_topology.
    + exact topology.
    + apply echo_ir_update_process_some_preserves_parent_edges.
      * exact (proj1 topology).
      * unfold echo_ir_parent_witness, echo_ir_parent_value in parent_valid.
        rewrite parent_value in parent_valid. exact parent_valid.
    + exact receiver_in.
    + intros receiver [same | impossible]; [subst receiver | contradiction].
      unfold echo_ir_parent_witness, echo_ir_parent_value in parent_valid.
      rewrite parent_value in parent_valid. exact (parent_valid receiver_in).
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology action.
  unfold echo_ir_initiator_reply_more_rule in action.
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
  change (echo_ir_topology_well_formed config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (echo_ir_config_initiator node config)
        (IROptionNodeValue None)
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender message)
            (ir_list_node_value_contents
              (ir_processes state
                (echo_ir_config_initiator node config) EchoIRPending))))
        false)
      (ir_message_id message))).
  eapply echo_ir_updated_delivery_preserves_topology.
  - exact topology.
  - now apply echo_ir_update_process_none_preserves_parent_edges,
      (proj1 topology).
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  change (echo_ir_topology_well_formed config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (echo_ir_config_initiator node config)
        (IROptionNodeValue None) (IRListNodeValue []) true)
      (ir_message_id message))).
  eapply echo_ir_updated_delivery_preserves_topology.
  - exact topology.
  - now apply echo_ir_update_process_none_preserves_parent_edges,
      (proj1 topology).
Qed.

Lemma echo_ir_enabled_expected_parent
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates) rule = IRRuleEnabled ->
  In (IROptionIsSomeExpr
      (echo_ir_parent node (echo_ir_receiver node)))
    (ir_rule_guards rule) ->
  echo_ir_parent_value node state (ir_message_receiver message) =
    Some (echo_ir_parent_witness node state
      (ir_message_receiver message)).
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (IROptionIsSomeExpr
      (echo_ir_parent node (echo_ir_receiver node)))
    enabled member) as guard.
  unfold echo_ir_parent, echo_ir_receiver in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  unfold echo_ir_parent_witness.
  unfold echo_ir_parent_value.
  rewrite (ir_option_node_value_eta
    (ir_processes state (ir_message_receiver message) EchoIRParent))
    in guard |- *.
  cbn in guard |- *.
  destruct (ir_option_node_value_contents
    (ir_processes state
      (ir_message_receiver message) EchoIRParent))
    as [actual |]; [reflexivity | discriminate].
Qed.

Lemma echo_ir_enabled_initiator_receiver
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates) rule = IRRuleEnabled ->
  In (echo_ir_equal node (echo_ir_receiver node)
      (echo_ir_initiator node))
    (ir_rule_guards rule) ->
  ir_message_receiver message = echo_ir_config_initiator node config.
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_equal node (echo_ir_receiver node)
      (echo_ir_initiator node)) enabled member) as guard.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  injection guard as equal.
  unfold echo_ir_config_initiator.
  unfold ir_node_eqb in equal.
  destruct (node_eq (ir_message_receiver message)
    (ir_node_value_contents (ir_config_fields config EchoIRInitiator)))
    as [same | different].
  - exact same.
  - discriminate.
Qed.

Lemma echo_ir_initiator_request_action_preserves_topology
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_topology_well_formed config state ->
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  In (ir_message_sender message) (ir_config_nodes config) /\
  In (ir_message_sender message)
    (ir_config_neighbors config (echo_ir_config_initiator node config)) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros topology initiator_in target_valid action.
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
  change (echo_ir_topology_well_formed config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      EchoIRReply (echo_ir_config_initiator node config)
      [ir_message_sender message] [])).
  destruct topology as [parents queued].
  assert (removed : echo_ir_topology_well_formed config
    (ir_remove_selected_message state (ir_message_id message))).
  {
    split.
    - now apply echo_ir_remove_selected_preserves_parent_edges.
    - now apply echo_ir_remove_selected_preserves_queued_edges.
  }
  destruct removed as [removed_parents removed_queued]. split.
  - now apply echo_ir_emit_preserves_parent_edges.
  - eapply echo_ir_emit_preserves_queued_edges.
    + exact removed_queued.
    + exact initiator_in.
    + intros receiver [same | impossible]; [subst receiver | contradiction].
      exact target_valid.
Qed.

Theorem EchoStep_preserves_topology_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric config ->
  echo_ir_topology_well_formed config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_topology_well_formed config successor.
Proof.
  intros initiator_in neighbors_valid symmetric topology step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected
        [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in.
  cbn in selected_in.
  destruct selected_in as [same | selected_in].
  - subst selected_rule.
    pose proof (eval_ir_rule_enabled_pattern node_eq config state
      runtime_event (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_action_preserves_topology.
    + exact topology.
    + exact initiator_in.
    + intros receiver receiver_in.
      pose proof (@echo_ir_start_enabled_order
        node node_eq config state certificates enabled) as permutation.
      assert (configured_neighbor :
        In receiver (ir_config_neighbors config
          (echo_ir_config_initiator node config))).
      { eapply Permutation_in; eauto. }
      destruct (neighbors_valid
        (echo_ir_config_initiator node config) initiator_in)
        as [_ valid].
      exact (valid receiver configured_neighbor).
    + exact action.
  - destruct selected_in as [same | selected_in].
    + subst selected_rule.
      pose proof (eval_ir_rule_enabled_pattern node_eq config state
        runtime_event (@echo_ir_first_request_nonleaf_rule node) enabled)
        as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_resolved_delivery_queued
        state external_event message certificates resolved) as queued.
      pose proof ((proj2 topology) message queued) as message_edge.
      destruct message_edge as [sender_in [receiver_in forward_edge]].
      assert (reverse_valid :
        In (ir_message_sender message) (ir_config_nodes config) /\
        In (ir_message_sender message)
          (ir_config_neighbors config (ir_message_receiver message))).
      { split; [exact sender_in | eapply symmetric; eauto]. }
      eapply echo_ir_first_request_nonleaf_action_preserves_topology.
      * exact topology.
      * exact receiver_in.
      * intros _. exact reverse_valid.
      * intros receiver receiver_ordered.
        pose proof (@echo_ir_nonleaf_enabled_order
          node node_eq config state message certificates enabled)
          as permutation.
        assert (remaining : In receiver
          (ir_remove_node node_eq (ir_message_sender message)
            (ir_config_neighbors config (ir_message_receiver message)))).
        { eapply Permutation_in; eauto. }
        pose proof (@echo_ir_remove_node_in node node_eq
          (ir_message_sender message) receiver
          (ir_config_neighbors config (ir_message_receiver message))
          remaining) as configured_neighbor.
        destruct (neighbors_valid (ir_message_receiver message) receiver_in)
          as [_ valid].
        exact (valid receiver configured_neighbor).
      * exact action.
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_resolved_delivery_queued
          state external_event message certificates resolved) as queued.
        pose proof ((proj2 topology) message queued) as message_edge.
        destruct message_edge as [sender_in [receiver_in forward_edge]].
        eapply echo_ir_first_request_leaf_action_preserves_topology.
        -- exact topology.
        -- exact receiver_in.
        -- intros _. split; [exact sender_in | eapply symmetric; eauto].
        -- exact action.
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           pose proof (echo_ir_resolved_delivery_queued
             state external_event message certificates resolved) as queued.
           pose proof ((proj2 topology) message queued) as message_edge.
           destruct message_edge as [sender_in [receiver_in forward_edge]].
           eapply echo_ir_message_reply_action_preserves_topology
             with (rule := @echo_ir_repeated_request_rule node).
           ++ reflexivity.
           ++ exact topology.
           ++ exact receiver_in.
           ++ split; [exact sender_in | eapply symmetric; eauto].
           ++ exact action.
        -- destruct selected_in as [same | selected_in].
           ++ subst selected_rule.
              pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              pose proof (echo_ir_resolved_delivery_queued
                state external_event message certificates resolved) as queued.
              pose proof ((proj2 topology) message queued) as message_edge.
              destruct message_edge as
                [sender_in [receiver_in forward_edge]].
              pose proof (echo_ir_enabled_initiator_receiver
                config state message certificates
                (@echo_ir_initiator_request_rule node) enabled
                ltac:(cbn [echo_ir_initiator_request_rule]; now left))
                as receiver_root.
              eapply echo_ir_initiator_request_action_preserves_topology.
              ** exact topology.
              ** exact initiator_in.
              ** split.
                 --- exact sender_in.
                 --- rewrite <- receiver_root. eapply symmetric; eauto.
              ** exact action.
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
                 pose proof (echo_ir_resolved_delivery_queued
                   state external_event message certificates resolved)
                   as queued.
                 pose proof ((proj2 topology) message queued) as message_edge.
                 destruct message_edge as
                   [sender_in [receiver_in forward_edge]].
                 assert (parent_equal := echo_ir_enabled_expected_parent
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)).
                 eapply
                   echo_ir_participant_reply_more_action_preserves_topology.
                 --- exact topology.
                 --- intro receiver_configured.
                     eapply (proj1 topology).
                     +++ exact receiver_configured.
                     +++ exact parent_equal.
                 --- exact action.
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
                     pose proof (echo_ir_resolved_delivery_queued
                       state external_event message certificates resolved)
                       as queued.
                     pose proof ((proj2 topology) message queued)
                       as message_edge.
                     destruct message_edge as
                       [sender_in [receiver_in forward_edge]].
                     assert (parent_equal := echo_ir_enabled_expected_parent
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)).
                     eapply
                       echo_ir_participant_reply_final_action_preserves_topology.
                     +++ exact topology.
                     +++ exact receiver_in.
                     +++ intro receiver_configured.
                         eapply (proj1 topology).
                         *** exact receiver_configured.
                         *** exact parent_equal.
                     +++ exact action.
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
                         exact
                           (echo_ir_initiator_reply_more_action_preserves_topology
                             config state successor message certificates
                             topology action).
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
                             exact
                               (echo_ir_initiator_reply_final_action_preserves_topology
                                 config state successor message certificates
                                 topology action).
                         *** contradiction.
Qed.

Lemma echo_ir_initial_topology_well_formed
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_topology_well_formed config (@echo_initial_state node).
Proof.
  split.
  - intros child parent child_in parent_value. discriminate.
  - intros message queued. contradiction.
Qed.

Theorem echo_ir_path_preserves_topology_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_topology_well_formed config initial ->
  echo_ir_topology_well_formed config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro topology.
  - exact topology.
  - apply IHreachable.
    eapply EchoStep_preserves_topology_well_formed.
    + exact initiator_in.
    + exact neighbors_valid.
    + exact symmetric.
    + exact topology.
    + exists rule. exact H.
Qed.

Theorem echo_reachable_topology_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric config ->
  echo_reachable node node_eq config state ->
  echo_ir_topology_well_formed config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  eapply echo_ir_path_preserves_topology_well_formed.
  - exact initiator_in.
  - exact neighbors_valid.
  - exact symmetric.
  - exact reachable.
  - apply echo_ir_initial_topology_well_formed.
Qed.

End EchoIRExecutableTopology.
