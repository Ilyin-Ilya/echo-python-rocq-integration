(** * Encoding the current executable Echo types into the generic IR

    This module is deliberately temporary migration infrastructure.  It gives
    old and generic executions a precise shared boundary while semantic
    equivalence is proved and the old Echo-specific IR remains the oracle. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR EchoRunner
  ProtocolIRTypes ProtocolIRExpressions ProtocolIRInterpreter ProtocolIRRunner
  EchoIRSignature EchoIRProgram EchoExecutableReachability
  EchoExecutableCorrect.

Section EchoIRCompatibility.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.
Variable config : @echo_config node.

Definition echo_ir_encode_kind (kind : echo_kind) : echo_ir_message_kind :=
  match kind with
  | EchoRequest => EchoIRRequest
  | EchoReply => EchoIRReply
  end.

Definition echo_ir_encode_process
    (process : @echo_process node) :
    ir_local_store node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_local_field_type echo_ir_signature selected) with
    | EchoIRParent => IROptionNodeValue (process_parent process)
    | EchoIRPending => IRListNodeValue (process_pending process)
    | EchoIRFinished => IRBoolValue (process_finished process)
    end.

Definition echo_ir_encode_globals
    (state : @executable_echo_state node) :
    ir_global_store node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_global_field_type echo_ir_signature selected) with
    | EchoIRStarted => IRBoolValue (started state)
    end.

Definition echo_ir_encode_config_fields :
    ir_config_store node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_config_field_type echo_ir_signature selected) with
    | EchoIRInitiator => IRNodeValue (config_initiator config)
    end.

Definition echo_ir_encode_config :
    ir_protocol_config node echo_ir_signature :=
  mkIRProtocolConfig
    (config_nodes config)
    (fun process =>
      nbrs (config_nodes config) (config_adjacent config) process)
    echo_ir_encode_config_fields.

Definition echo_ir_encode_message
    (message : @echo_message node) :
    ir_message node echo_ir_signature :=
  @mkIRMessage node echo_ir_signature
    (message_id message)
    (echo_ir_encode_kind (message_kind message))
    (message_sender message)
    (message_receiver message)
    [].

Definition echo_ir_encode_state
    (state : @executable_echo_state node) :
    ir_protocol_state node echo_ir_signature :=
  @mkIRProtocolState node echo_ir_signature
    (fun process => echo_ir_encode_process (processes state process))
    (List.map echo_ir_encode_message (message_store state))
    (echo_ir_encode_globals state)
    (next_message_id state).

Definition echo_ir_start_certificates
    (ordered_neighbors : list node) :
    ir_start_certificates node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_start_certificate_field_type
          echo_ir_signature selected) with
    | EchoIRStartOrder => IRListNodeValue ordered_neighbors
    end.

Definition echo_ir_event_forward_order
    (event : @echo_event node) : list node :=
  match event with
  | EchoFirstRequestNonLeaf _ ordered => ordered
  | _ => []
  end.

Definition echo_ir_event_expected_parent
    (event : @echo_event node) : node :=
  match event with
  | EchoParticipantReplyMore _ parent
  | EchoParticipantReplyFinal _ parent => parent
  | _ => config_initiator config
  end.

Definition echo_ir_delivery_certificates
    (event : @echo_event node) :
    ir_delivery_certificates node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_delivery_certificate_field_type
          echo_ir_signature selected) with
    | EchoIRForwardOrder =>
        IRListNodeValue (echo_ir_event_forward_order event)
    | EchoIRExpectedParent =>
        IRNodeValue (echo_ir_event_expected_parent event)
    end.

(** Typed projections used when reconstructing an old migration event from a
    generic delivery.  The generic scheduler supplies certificates as a field
    map; these functions expose the two Echo-specific witness values without
    giving the scheduler control over rule selection. *)
Definition echo_ir_delivery_forward_order_value
    (certificates : ir_delivery_certificates node echo_ir_signature) :
    list node :=
  ir_list_node_value_contents (certificates EchoIRForwardOrder).

Definition echo_ir_delivery_expected_parent_value
    (certificates : ir_delivery_certificates node echo_ir_signature) :
    node :=
  ir_node_value_contents (certificates EchoIRExpectedParent).

Definition echo_ir_encode_event
    (event : @echo_event node) :
    ir_external_event node echo_ir_signature :=
  match event with
  | EchoStart ordered_neighbors =>
      IRProtocolStart (echo_ir_start_certificates ordered_neighbors)
  | EchoFirstRequestNonLeaf message _
  | EchoFirstRequestLeaf message
  | EchoRepeatedRequest message
  | EchoInitiatorRequest message
  | EchoParticipantReplyMore message _
  | EchoParticipantReplyFinal message _
  | EchoInitiatorReplyMore message
  | EchoInitiatorReplyFinal message =>
      IRProtocolDeliver
        (message_id message)
        (echo_ir_delivery_certificates event)
  end.

Lemma echo_ir_find_encoded_message
    (messages : list (@echo_message node))
    (selected : @echo_message node) :
  NoDup (List.map message_id messages) ->
  In selected messages ->
  ir_find_message (message_id selected)
    (List.map echo_ir_encode_message messages) =
  Some (echo_ir_encode_message selected).
Proof.
  revert selected.
  induction messages as [|candidate rest IH];
    intros selected identifiers_unique selected_in.
  - contradiction.
  - inversion identifiers_unique as [|identifier identifiers
      candidate_id_not_in rest_ids_unique].
    cbn [ir_find_message echo_ir_encode_message].
    destruct selected_in as [same | selected_in].
    + subst selected.
      change
        ((if Nat.eqb (message_id candidate) (message_id candidate)
         then Some (echo_ir_encode_message candidate)
         else ir_find_message (message_id candidate)
           (List.map echo_ir_encode_message rest)) =
        Some (echo_ir_encode_message candidate)).
      now rewrite Nat.eqb_refl.
    + destruct (Nat.eqb (message_id selected) (message_id candidate))
        eqn:same_identifier.
      * apply Nat.eqb_eq in same_identifier. exfalso.
        apply candidate_id_not_in.
        apply in_map_iff. exists selected. split.
        -- now symmetry.
        -- exact selected_in.
      * change
          ((if Nat.eqb (message_id selected) (message_id candidate)
            then Some (echo_ir_encode_message candidate)
            else ir_find_message (message_id selected)
              (List.map echo_ir_encode_message rest)) =
           Some (echo_ir_encode_message selected)).
        rewrite same_identifier. now apply IH.
Qed.

(** Resolving an arbitrary generic delivery over an encoded old state always
    exposes an encoding of an authoritative old queued message.  This is the
    reverse-direction companion of [echo_ir_find_encoded_message]: callers do
    not need to trust a duplicated message record supplied by the scheduler. *)
Lemma echo_ir_resolved_delivery_source
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (runtime_event : ir_runtime_event node echo_ir_signature) :
  ir_resolve_event (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) = Some runtime_event ->
  exists message,
    In message (message_store state) /\
    selected_id = message_id message /\
    runtime_event = IRRuntimeDeliver
      (echo_ir_encode_message message) certificates.
Proof.
  intro resolved.
  destruct (resolved_delivery_was_queued
    (echo_ir_encode_state state) selected_id certificates runtime_event
    resolved) as
    [encoded_message [encoded_queued [selected_identifier runtime_is_delivery]]].
  cbn [echo_ir_encode_state ir_message_store] in encoded_queued.
  apply in_map_iff in encoded_queued.
  destruct encoded_queued as [message [encoded_equal queued]].
  subst encoded_message.
  exists message. repeat split.
  - exact queued.
  - exact selected_identifier.
  - exact runtime_is_delivery.
Qed.

(** A reachable successful delivery cannot make the generic bridge resolve an
    ID to a different message.  Reachability supplies unique queued IDs; the
    old successful step supplies exact queue membership. *)
Theorem echo_ir_resolve_successful_delivery
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state event successor ->
  is_delivery_event event ->
  ir_resolve_event
    (echo_ir_encode_state state)
    (echo_ir_encode_event event) =
  Some (IRRuntimeDeliver
    (echo_ir_encode_message (@event_message node config event))
    (echo_ir_delivery_certificates event)).
Proof.
  intros reachable step delivery.
  pose proof (@echo_reachable_message_ids_well_formed
    node node_eq config state reachable) as [_ identifiers_unique].
  pose proof (@EchoStep_delivery_message_queued
    node node_eq config state successor event step delivery) as queued.
  destruct event; cbn [is_delivery_event] in delivery; try contradiction.
  all: cbv beta iota zeta delta [echo_ir_encode_event ir_resolve_event
    echo_ir_encode_state ir_message_store].
  all: rewrite (echo_ir_find_encoded_message
    (message_store state) message identifiers_unique queued).
  all: reflexivity.
Qed.

Theorem echo_ir_encode_initial_state :
  echo_ir_encode_state initial_executable_echo_state =
  initialize_ir_protocol (@echo_ir_program node).
Proof.
  reflexivity.
Qed.

Theorem echo_ir_complete_encoding (state : @executable_echo_state node) :
  eval_ir_state_predicate node_eq echo_ir_encode_config
    (echo_ir_encode_state state) (@echo_ir_complete_expr node) =
  Some (echo_completeb config state).
Proof.
  unfold eval_ir_state_predicate, echo_completeb.
  unfold echo_ir_encode_config, echo_ir_encode_config_fields,
    echo_ir_encode_state, echo_ir_encode_process, echo_ir_encode_globals.
  cbn [echo_ir_complete_expr echo_ir_started echo_ir_is_empty
    echo_ir_pending echo_ir_initiator echo_ir_finished
    echo_ir_neighbors echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    eval_ir_expr echo_list_emptyb ir_global_fields ir_config_fields
    ir_processes ir_message_store ir_config_neighbors echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type].
  destruct (started state);
    destruct (process_pending
      (processes state (config_initiator config)));
    destruct (message_store state);
    destruct (process_finished
      (processes state (config_initiator config)));
    destruct (nbrs (config_nodes config) (config_adjacent config)
      (config_initiator config));
    reflexivity.
Qed.

Theorem echo_ir_stuck_encoding (state : @executable_echo_state node) :
  eval_ir_state_predicate node_eq echo_ir_encode_config
    (echo_ir_encode_state state) (@echo_ir_stuck_expr node) =
  Some (echo_stuckb state).
Proof.
  unfold eval_ir_state_predicate, echo_stuckb.
  unfold echo_ir_encode_config, echo_ir_encode_config_fields,
    echo_ir_encode_state, echo_ir_encode_process, echo_ir_encode_globals.
  cbn [echo_ir_stuck_expr echo_ir_started
    echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    eval_ir_expr echo_list_emptyb ir_global_fields ir_config_fields
    ir_processes ir_message_store echo_ir_signature
    echo_ir_global_field_type].
  destruct (started state); destruct (message_store state); reflexivity.
Qed.

End EchoIRCompatibility.

Arguments echo_ir_encode_config {node} config.
Arguments echo_ir_encode_state {node} _.
Arguments echo_ir_encode_event {node} config _.
