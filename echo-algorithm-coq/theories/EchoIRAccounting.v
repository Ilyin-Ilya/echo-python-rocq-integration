(** * Discovery and request/reply accounting on generic Echo IR states

    These statements expose Echo accounting invariants at the generic program
    boundary.  Their public predicates mention only generic IR states and
    generated identifiers.  All results are proved directly from the generic
    interpreter and its generated Echo program. *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoTopology ProtocolIRTypes ProtocolIRRunner
  EchoIRSignature EchoIRConfig EchoIRProgram EchoIRExecutableDiscovery
  EchoIRExecutableRequestAccounting EchoIRExecutableRequestParent
  EchoIRExecutableReplyDiscovery EchoIRExecutableRequestReply
  EchoIRSafety.

Module MakeEchoIRAccounting (C : ECHO_CORRECTNESS_CONFIG).

Module Safety := MakeEchoIRSafety C.
Module Tree := Safety.Tree.

Local Notation node := C.node.
Local Notation node_eq := C.node_eq.
Local Notation initiator := C.initiator.
Local Notation all_nodes := C.all_nodes.
Local Notation adj := C.adj.
Local Notation ir_config :=
  (make_echo_ir_config initiator all_nodes adj).
Local Notation ir_program := (@echo_ir_program node).

(** A process is discovered exactly when at least one observable local field
    differs from the generated initial local state.  Keeping this definition
    field-based avoids function extensionality for dependent local stores. *)
Definition echo_ir_discovered
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : Prop :=
  Tree.echo_ir_parent state owner <> None \/
  Safety.echo_ir_pending state owner <> [] \/
  Safety.echo_ir_finished state owner <> false.

Definition echo_ir_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall first second,
    In first (ir_message_store state) ->
    In second (ir_message_store state) ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.

Definition echo_ir_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    Tree.echo_ir_parent state (ir_message_receiver message) <>
      Some (ir_message_sender message).

Definition echo_ir_reply_receivers_discovered
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    echo_ir_discovered state (ir_message_receiver message).

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

(** Every discovered configured participant has installed an IR parent. *)
Theorem echo_ir_reachable_discovered_participants_parented
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  forall owner,
    In owner all_nodes ->
    owner <> initiator ->
    echo_ir_discovered ir_state owner ->
    exists parent,
      Tree.echo_ir_parent ir_state owner = Some parent.
Proof.
  intros reachable owner owner_in not_initiator discovered.
  pose proof
    (@EchoIRExecutableDiscovery.echo_reachable_discovered_participants_parented
      node node_eq ir_config ir_state reachable) as direct.
  unfold EchoIRExecutableDiscovery.echo_ir_discovered_participants_parented,
    EchoIRExecutableInvariants.echo_ir_config_initiator in direct.
  unfold ir_config, make_echo_ir_config,
    echo_ir_config_fields in direct.
  cbn [ir_config_fields ir_node_value_contents] in direct.
  specialize (direct owner not_initiator).
  assert (local_discovered :
    EchoIRExecutableDiscovery.echo_ir_local_discovered node ir_state owner).
  {
    unfold EchoIRExecutableDiscovery.echo_ir_local_discovered,
      EchoIRExecutableDiscovery.echo_ir_parent_value,
      EchoIRExecutableDiscovery.echo_ir_pending_value,
      EchoIRExecutableDiscovery.echo_ir_finished_value.
    unfold echo_ir_discovered, Tree.echo_ir_parent,
      Safety.echo_ir_pending, Safety.echo_ir_finished in discovered.
    exact discovered.
  }
  destruct (direct local_discovered) as [parent parent_value].
  exists parent.
  unfold Tree.echo_ir_parent.
  exact parent_value.
Qed.

(** At most one queued request occupies a directed edge. *)
Theorem echo_ir_reachable_request_edges_unique
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_request_edges_unique ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableRequestAccounting.echo_reachable_request_edges_unique
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableRequestAccounting.echo_ir_request_edges_unique
    in direct.
  exact direct.
Qed.

(** A queued request never points from an installed parent to its child. *)
Theorem echo_ir_reachable_request_parent_distinct
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_request_parent_distinct ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableRequestParent.echo_reachable_request_parent_distinct
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableRequestParent.echo_ir_request_parent_distinct
    in direct.
  unfold echo_ir_request_parent_distinct, Tree.echo_ir_parent.
  exact direct.
Qed.

(** Every queued IR reply targets a process that has been discovered. *)
Theorem echo_ir_reachable_reply_receivers_discovered
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_reply_receivers_discovered ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableReplyDiscovery.echo_reachable_reply_receivers_discovered
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableReplyDiscovery.echo_ir_reply_receivers_discovered
    in direct.
  unfold echo_ir_reply_receivers_discovered.
  intros message queued reply_kind.
  specialize (direct message queued reply_kind).
  unfold EchoIRExecutableDiscovery.echo_ir_local_discovered,
    EchoIRExecutableDiscovery.echo_ir_parent_value,
    EchoIRExecutableDiscovery.echo_ir_pending_value,
    EchoIRExecutableDiscovery.echo_ir_finished_value in direct.
  unfold echo_ir_discovered, Tree.echo_ir_parent,
    Safety.echo_ir_pending, Safety.echo_ir_finished.
  exact direct.
Qed.

(** A queued request cannot coexist with its reverse reply. *)
Theorem echo_ir_reachable_request_reply_reverse_distinct
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_request_reply_reverse_distinct ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableRequestReply.echo_reachable_request_reply_reverse_distinct
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableRequestReply.echo_ir_request_reply_reverse_distinct
    in direct.
  exact direct.
Qed.

End MakeEchoIRAccounting.
