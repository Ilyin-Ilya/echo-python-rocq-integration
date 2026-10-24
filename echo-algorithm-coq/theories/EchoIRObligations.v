(** * Queue and pending-obligation invariants on generic Echo IR states

    This module completes the invariant migration needed for the generic Echo
    program.  Public statements use generic state/message projections and are
    proved directly over execution of the generated generic IR program. *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoTopology ProtocolIRTypes
  ProtocolIRRunner EchoIRSignature EchoIRConfig EchoIRProgram
  EchoIRAccounting.
Require Import EchoIRExecutableObligations.

Module MakeEchoIRObligations (C : ECHO_CORRECTNESS_CONFIG).

Module Accounting := MakeEchoIRAccounting C.
Module Safety := Accounting.Safety.
Module Tree := Accounting.Tree.

Local Notation node := C.node.
Local Notation node_eq := C.node_eq.
Local Notation initiator := C.initiator.
Local Notation all_nodes := C.all_nodes.
Local Notation adj := C.adj.
Local Notation ir_config :=
  (make_echo_ir_config initiator all_nodes adj).
Local Notation ir_program := (@echo_ir_program node).

Definition echo_ir_reply_noninitiator_senders_discovered
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    ir_message_sender message <> initiator ->
    Accounting.echo_ir_discovered state (ir_message_sender message).

Definition echo_ir_parent_replies_from_finished
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    Tree.echo_ir_parent state (ir_message_sender message) =
      Some (ir_message_receiver message) ->
    Safety.echo_ir_finished state (ir_message_sender message) = true.

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

Definition echo_ir_queued_requests_pending
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    In (ir_message_receiver message)
      (Safety.echo_ir_pending state (ir_message_sender message)).

Definition echo_ir_unfinished_children_pending
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall child parent,
    In child all_nodes ->
    Tree.echo_ir_parent state child = Some parent ->
    Safety.echo_ir_finished state child = false ->
    In child (Safety.echo_ir_pending state parent).

Definition echo_ir_queued_replies_pending
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    In (ir_message_sender message)
      (Safety.echo_ir_pending state (ir_message_receiver message)).

Theorem echo_ir_reachable_reply_noninitiator_senders_discovered
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_reply_noninitiator_senders_discovered ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_reply_noninitiator_senders_discovered
      node node_eq ir_config ir_state reachable) as direct.
  unfold
    EchoIRExecutableObligations.echo_ir_reply_noninitiator_senders_discovered
    in direct.
  unfold echo_ir_reply_noninitiator_senders_discovered.
  intros message queued reply_kind not_initiator.
  specialize (direct message queued reply_kind).
  unfold ir_config, make_echo_ir_config, echo_ir_config_fields,
    EchoIRExecutableInvariants.echo_ir_config_initiator in direct.
  cbn [ir_config_fields ir_node_value_contents] in direct.
  specialize (direct not_initiator).
  unfold EchoIRExecutableDiscovery.echo_ir_local_discovered,
    EchoIRExecutableDiscovery.echo_ir_parent_value,
    EchoIRExecutableDiscovery.echo_ir_pending_value,
    EchoIRExecutableDiscovery.echo_ir_finished_value in direct.
  unfold Accounting.echo_ir_discovered, Tree.echo_ir_parent,
    Safety.echo_ir_pending, Safety.echo_ir_finished.
  exact direct.
Qed.

Theorem echo_ir_reachable_parent_replies_from_finished
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_parent_replies_from_finished ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_parent_replies_from_finished
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableObligations.echo_ir_parent_replies_from_finished
    in direct.
  unfold echo_ir_parent_replies_from_finished.
  intros message queued reply_kind parent_link.
  apply direct with (message := message); try assumption.
Qed.

Theorem echo_ir_reachable_reply_edges_unique
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_reply_edges_unique ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_reply_edges_unique
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableObligations.echo_ir_reply_edges_unique in direct.
  exact direct.
Qed.

Theorem echo_ir_reachable_queued_requests_pending
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_queued_requests_pending ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_queued_requests_pending
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableObligations.echo_ir_queued_requests_pending in direct.
  unfold echo_ir_queued_requests_pending.
  intros message queued request_kind.
  specialize (direct message queued request_kind).
  unfold EchoIRExecutableDiscovery.echo_ir_pending_value in direct.
  exact direct.
Qed.

Theorem echo_ir_reachable_unfinished_children_pending
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_unfinished_children_pending ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_unfinished_children_pending
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableObligations.echo_ir_unfinished_children_pending
    in direct.
  unfold echo_ir_unfinished_children_pending.
  intros child parent child_in parent_link unfinished.
  apply direct with (child := child) (parent := parent).
  - exact child_in.
  - exact parent_link.
  - exact unfinished.
Qed.

Theorem echo_ir_reachable_queued_replies_pending
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_queued_replies_pending ir_state.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_queued_replies_pending
      node node_eq ir_config ir_state
      Safety.echo_ir_encoded_initiator_configured
      Safety.echo_ir_encoded_neighbors_well_formed
      Safety.echo_ir_encoded_neighbors_symmetric reachable) as direct.
  unfold EchoIRExecutableObligations.echo_ir_queued_replies_pending in direct.
  unfold echo_ir_queued_replies_pending.
  intros message queued reply_kind.
  specialize (direct message queued reply_kind).
  unfold EchoIRExecutableDiscovery.echo_ir_pending_value in direct.
  exact direct.
Qed.

(** Any local pending item implies that the initiator still has a pending
    item.  The witness need not be the same node; only non-emptiness is
    propagated along the formally ranked parent chain. *)
Theorem echo_ir_reachable_pending_reaches_initiator
    (ir_state : ir_protocol_state node echo_ir_signature)
    (owner item : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In owner all_nodes ->
  In item (Safety.echo_ir_pending ir_state owner) ->
  exists root_item,
    In root_item (Safety.echo_ir_pending ir_state initiator).
Proof.
  intros reachable owner_in item_pending.
  eapply
    (@EchoIRExecutableObligations.echo_reachable_pending_reaches_initiator
      node node_eq ir_config ir_state owner item).
  - exact Safety.echo_ir_encoded_initiator_configured.
  - exact Safety.echo_ir_encoded_neighbors_well_formed.
  - exact Safety.echo_ir_encoded_neighbors_symmetric.
  - exact reachable.
  - exact owner_in.
  - exact item_pending.
Qed.

(** Every queued generic message therefore witnesses a nonempty initiator
    pending list. *)
Theorem echo_ir_reachable_queued_message_initiator_pending
    (ir_state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In message (ir_message_store ir_state) ->
  exists root_item,
    In root_item (Safety.echo_ir_pending ir_state initiator).
Proof.
  intros reachable queued.
  destruct (ir_message_kind message) eqn:kind.
  - pose proof (echo_ir_reachable_queued_requests_pending ir_state reachable
      message queued kind) as pending.
    eapply echo_ir_reachable_pending_reaches_initiator.
    + exact reachable.
    + pose proof (Safety.echo_ir_reachable_queued_edges_valid
        ir_state reachable message queued) as [sender_in rest].
      exact sender_in.
    + exact pending.
  - pose proof (echo_ir_reachable_queued_replies_pending ir_state reachable
      message queued kind) as pending.
    eapply echo_ir_reachable_pending_reaches_initiator.
    + exact reachable.
    + pose proof (Safety.echo_ir_reachable_queued_edges_valid
        ir_state reachable message queued) as
        [sender_in [receiver_in edge]].
      exact receiver_in.
    + exact pending.
Qed.

End MakeEchoIRObligations.
