(** * Typed, protocol-neutral values and state for generated protocols

    This file is the first layer of the generic protocol IR.  It deliberately
    contains no protocol-specific constructors.  A protocol supplies finite
    identifiers for its fields, message kinds, certificates, and diagnostic rule names; the
    signature assigns a type to every value-bearing identifier.

    Field stores are intrinsically typed: looking up a field whose signature
    says [IRNat] returns an [ir_value node IRNat].  Consequently a protocol
    action cannot install a Boolean in that field, either accidentally or via
    a failed dynamic cast. *)

From Stdlib Require Import List Bool Arith Logic.Eqdep_dec.
Import ListNotations.

(** The initial universe is intentionally small.  It covers the current
    reference model while leaving natural-number and message-reference
    capabilities for a differently shaped genericity test. *)
Inductive ir_type : Type :=
  | IRBool
  | IRNat
  | IRNode
  | IROptionNode
  | IRListNode
  | IRMessageRef.

Inductive ir_value (node : Type) : ir_type -> Type :=
  | IRBoolValue : bool -> ir_value node IRBool
  | IRNatValue : nat -> ir_value node IRNat
  | IRNodeValue : node -> ir_value node IRNode
  | IROptionNodeValue : option node -> ir_value node IROptionNode
  | IRListNodeValue : list node -> ir_value node IRListNode
  | IRMessageRefValue : nat -> ir_value node IRMessageRef.

Arguments IRBoolValue {node} _.
Arguments IRNatValue {node} _.
Arguments IRNodeValue {node} _.
Arguments IROptionNodeValue {node} _.
Arguments IRListNodeValue {node} _.
Arguments IRMessageRefValue {node} _.

(** Total projections for values whose type index fixes their constructor.
    The eta lemmas are proved by dependent pattern matching, without function
    extensionality or equality-proof axioms.  They let protocol bridges reason
    about typed certificate maps constructively. *)
Definition ir_node_value_contents
    {node : Type} (value : ir_value node IRNode) : node :=
  match value with
  | IRNodeValue item => item
  end.

Definition ir_list_node_value_contents
    {node : Type} (value : ir_value node IRListNode) : list node :=
  match value with
  | IRListNodeValue items => items
  end.

Definition ir_option_node_value_contents
    {node : Type} (value : ir_value node IROptionNode) : option node :=
  match value with
  | IROptionNodeValue item => item
  end.

Lemma ir_node_value_eta
    {node : Type} (value : ir_value node IRNode) :
  value = IRNodeValue (ir_node_value_contents value).
Proof.
  exact
    (match value as selected in ir_value _ kind return
      match kind as actual return ir_value node actual -> Prop with
      | IRNode => fun selected =>
          selected = IRNodeValue (ir_node_value_contents selected)
      | _ => fun _ => True
      end selected
    with
    | IRBoolValue _ => I
    | IRNatValue _ => I
    | IRNodeValue item => eq_refl
    | IROptionNodeValue _ => I
    | IRListNodeValue _ => I
    | IRMessageRefValue _ => I
    end).
Qed.

Lemma ir_list_node_value_eta
    {node : Type} (value : ir_value node IRListNode) :
  value = IRListNodeValue (ir_list_node_value_contents value).
Proof.
  exact
    (match value as selected in ir_value _ kind return
      match kind as actual return ir_value node actual -> Prop with
      | IRListNode => fun selected =>
          selected = IRListNodeValue (ir_list_node_value_contents selected)
      | _ => fun _ => True
      end selected
    with
    | IRBoolValue _ => I
    | IRNatValue _ => I
    | IRNodeValue _ => I
    | IROptionNodeValue _ => I
    | IRListNodeValue items => eq_refl
    | IRMessageRefValue _ => I
    end).
Qed.

Lemma ir_option_node_value_eta
    {node : Type} (value : ir_value node IROptionNode) :
  value = IROptionNodeValue (ir_option_node_value_contents value).
Proof.
  exact
    (match value as selected in ir_value _ kind return
      match kind as actual return ir_value node actual -> Prop with
      | IROptionNode => fun selected =>
          selected = IROptionNodeValue
            (ir_option_node_value_contents selected)
      | _ => fun _ => True
      end selected
    with
    | IRBoolValue _ => I
    | IRNatValue _ => I
    | IRNodeValue _ => I
    | IROptionNodeValue item => eq_refl
    | IRListNodeValue _ => I
    | IRMessageRefValue _ => I
    end).
Qed.

Definition ir_node_eqb
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (left right : node) : bool :=
  if node_eq_dec left right then true else false.

Definition ir_option_node_eqb
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (left right : option node) : bool :=
  match left, right with
  | None, None => true
  | Some left_node, Some right_node =>
      ir_node_eqb node_eq_dec left_node right_node
  | _, _ => false
  end.

Fixpoint ir_node_list_eqb
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (left right : list node) : bool :=
  match left, right with
  | [], [] => true
  | left_node :: left_rest, right_node :: right_rest =>
      ir_node_eqb node_eq_dec left_node right_node &&
        ir_node_list_eqb node_eq_dec left_rest right_rest
  | _, _ => false
  end.

Definition ir_value_eqb
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    {kind : ir_type}
    (left right : ir_value node kind) : bool :=
  match left in ir_value _ selected
    return ir_value node selected -> bool with
  | IRBoolValue left_value =>
      fun right_value =>
        match right_value with
        | IRBoolValue value => Bool.eqb left_value value
        end
  | IRNatValue left_value =>
      fun right_value =>
        match right_value with
        | IRNatValue value => Nat.eqb left_value value
        end
  | IRNodeValue left_value =>
      fun right_value =>
        match right_value with
        | IRNodeValue value => ir_node_eqb node_eq_dec left_value value
        end
  | IROptionNodeValue left_value =>
      fun right_value =>
        match right_value with
        | IROptionNodeValue value =>
            ir_option_node_eqb node_eq_dec left_value value
        end
  | IRListNodeValue left_value =>
      fun right_value =>
        match right_value with
        | IRListNodeValue value =>
            ir_node_list_eqb node_eq_dec left_value value
        end
  | IRMessageRefValue left_value =>
      fun right_value =>
        match right_value with
        | IRMessageRefValue value => Nat.eqb left_value value
        end
  end right.

(** All identifier types are protocol parameters.  Equality evidence is kept
    in the signature because both Rocq execution and generated runtimes must be
    able to update finite field maps and identify rule/message constructors. *)
Record protocol_signature : Type := mkProtocolSignature {
  signature_local_field : Type;
  signature_local_field_eq_dec :
    forall left right : signature_local_field,
      {left = right} + {left <> right};
  signature_local_field_type : signature_local_field -> ir_type;

  signature_global_field : Type;
  signature_global_field_eq_dec :
    forall left right : signature_global_field,
      {left = right} + {left <> right};
  signature_global_field_type : signature_global_field -> ir_type;

  signature_config_field : Type;
  signature_config_field_eq_dec :
    forall left right : signature_config_field,
      {left = right} + {left <> right};
  signature_config_field_type : signature_config_field -> ir_type;

  signature_message_kind : Type;
  signature_message_kind_eq_dec :
    forall left right : signature_message_kind,
      {left = right} + {left <> right};

  signature_payload_field : Type;
  signature_payload_field_eq_dec :
    forall left right : signature_payload_field,
      {left = right} + {left <> right};
  signature_payload_field_type : signature_payload_field -> ir_type;

  signature_start_certificate_field : Type;
  signature_start_certificate_field_eq_dec :
    forall left right : signature_start_certificate_field,
      {left = right} + {left <> right};
  signature_start_certificate_field_type :
    signature_start_certificate_field -> ir_type;

  signature_delivery_certificate_field : Type;
  signature_delivery_certificate_field_eq_dec :
    forall left right : signature_delivery_certificate_field,
      {left = right} + {left <> right};
  signature_delivery_certificate_field_type :
    signature_delivery_certificate_field -> ir_type;

  signature_rule_id : Type;
  signature_rule_id_eq_dec :
    forall left right : signature_rule_id,
      {left = right} + {left <> right}
}.

(** Local, global, configuration, and certificate stores are total typed maps.
    Protocol initialization supplies a value for every declared field; no
    untyped "missing value" case is needed. *)
Definition ir_field_store
    (node field : Type) (field_type : field -> ir_type) : Type :=
  forall selected : field, ir_value node (field_type selected).

Definition ir_local_store
    (node : Type) (signature : protocol_signature) : Type :=
  ir_field_store node
    (signature_local_field signature)
    (signature_local_field_type signature).

Definition ir_global_store
    (node : Type) (signature : protocol_signature) : Type :=
  ir_field_store node
    (signature_global_field signature)
    (signature_global_field_type signature).

Definition ir_config_store
    (node : Type) (signature : protocol_signature) : Type :=
  ir_field_store node
    (signature_config_field signature)
    (signature_config_field_type signature).

(** Message payloads are typed association lists rather than total maps because
    different message kinds can carry different subsets of the protocol's
    payload fields.  Every stored entry still carries the value type assigned
    to its field by the signature. *)
Inductive ir_payload_entry
    (node : Type) (signature : protocol_signature) : Type :=
  | mkIRPayloadEntry : forall field : signature_payload_field signature,
      ir_value node (signature_payload_field_type signature field) ->
      ir_payload_entry node signature.

Arguments mkIRPayloadEntry {node signature} _ _.

Definition ir_payload_store
    (node : Type) (signature : protocol_signature) : Type :=
  list (ir_payload_entry node signature).

Fixpoint ir_payload_lookup
    {node : Type} {signature : protocol_signature}
    (field : signature_payload_field signature)
    (payload : ir_payload_store node signature) :
    option (ir_value node (signature_payload_field_type signature field)) :=
  match payload with
  | [] => None
  | mkIRPayloadEntry candidate value :: rest =>
      match signature_payload_field_eq_dec signature field candidate with
      | left equal =>
          Some
            (eq_rect candidate
              (fun selected =>
                ir_value node
                  (signature_payload_field_type signature selected))
              value field (eq_sym equal))
      | right _ => ir_payload_lookup field rest
      end
  end.

Definition ir_start_certificates
    (node : Type) (signature : protocol_signature) : Type :=
  ir_field_store node
    (signature_start_certificate_field signature)
    (signature_start_certificate_field_type signature).

Definition ir_delivery_certificates
    (node : Type) (signature : protocol_signature) : Type :=
  ir_field_store node
    (signature_delivery_certificate_field signature)
    (signature_delivery_certificate_field_type signature).

Record ir_message (node : Type) (signature : protocol_signature) : Type :=
  mkIRMessage {
    ir_message_id : nat;
    ir_message_kind : signature_message_kind signature;
    ir_message_sender : node;
    ir_message_receiver : node;
    ir_message_payload : ir_payload_store node signature
  }.

Arguments mkIRMessage {node signature} _ _ _ _ _.
Arguments ir_message_id {node signature} _.
Arguments ir_message_kind {node signature} _.
Arguments ir_message_sender {node signature} _.
Arguments ir_message_receiver {node signature} _.
Arguments ir_message_payload {node signature} _.

Fixpoint ir_find_message
    {node : Type} {signature : protocol_signature}
    (selected_id : nat)
    (messages : list (ir_message node signature)) :
    option (ir_message node signature) :=
  match messages with
  | [] => None
  | message :: rest =>
      if Nat.eqb selected_id (ir_message_id message)
      then Some message
      else ir_find_message selected_id rest
  end.

Lemma ir_find_message_sound
    {node : Type} {signature : protocol_signature}
    (selected_id : nat)
    (messages : list (ir_message node signature))
    (message : ir_message node signature) :
  ir_find_message selected_id messages = Some message ->
  In message messages /\ selected_id = ir_message_id message.
Proof.
  induction messages as [|candidate rest IH]; cbn.
  - discriminate.
  - destruct (Nat.eqb selected_id (ir_message_id candidate))
      eqn:identifier_equal.
    + intro found. inversion found. subst candidate.
      split.
      * now left.
      * now apply Nat.eqb_eq in identifier_equal.
    + intro found. apply IH in found as [in_rest identifier_matches].
      split.
      * now right.
      * exact identifier_matches.
Qed.

(** Topology is exposed through a deterministic neighbor-list view.  Protocol
    expressions can inspect it but cannot replace it during execution. *)
Record ir_protocol_config
    (node : Type) (signature : protocol_signature) : Type :=
  mkIRProtocolConfig {
    ir_config_nodes : list node;
    ir_config_neighbors : node -> list node;
    ir_config_fields : ir_config_store node signature
  }.

Arguments mkIRProtocolConfig {node signature} _ _ _.
Arguments ir_config_nodes {node signature} _.
Arguments ir_config_neighbors {node signature} _ _.
Arguments ir_config_fields {node signature} _ _.

Record ir_protocol_state
    (node : Type) (signature : protocol_signature) : Type :=
  mkIRProtocolState {
    ir_processes : node -> ir_local_store node signature;
    ir_message_store : list (ir_message node signature);
    ir_global_fields : ir_global_store node signature;
    ir_next_message_id : nat
  }.

Arguments mkIRProtocolState {node signature} _ _ _ _.
Arguments ir_processes {node signature} _ _ _.
Arguments ir_message_store {node signature} _.
Arguments ir_global_fields {node signature} _ _.
Arguments ir_next_message_id {node signature} _.

(** Observational equality for protocol states.  Stores are represented by
    functions, so ordinary record equality would require function
    extensionality even though every interpreter observation agrees.  This
    relation is the reusable equality notion for simulations and runners. *)
Definition ir_states_equivalent
    {node : Type} {signature : protocol_signature}
    (left right : ir_protocol_state node signature) : Prop :=
  (forall process field,
    ir_processes left process field = ir_processes right process field) /\
  ir_message_store left = ir_message_store right /\
  (forall field,
    ir_global_fields left field = ir_global_fields right field) /\
  ir_next_message_id left = ir_next_message_id right.

Lemma ir_states_equivalent_refl
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature) :
  ir_states_equivalent state state.
Proof.
  repeat split; reflexivity.
Qed.

Lemma ir_states_equivalent_sym
    {node : Type} {signature : protocol_signature}
    (left right : ir_protocol_state node signature) :
  ir_states_equivalent left right ->
  ir_states_equivalent right left.
Proof.
  intros [processes_equal
    [messages_equal [globals_equal next_id_equal]]].
  repeat split.
  - intros process field. symmetry. apply processes_equal.
  - now symmetry.
  - intro field. symmetry. apply globals_equal.
  - now symmetry.
Qed.

Lemma ir_states_equivalent_trans
    {node : Type} {signature : protocol_signature}
    (first second third : ir_protocol_state node signature) :
  ir_states_equivalent first second ->
  ir_states_equivalent second third ->
  ir_states_equivalent first third.
Proof.
  intros [first_processes
    [first_messages [first_globals first_next_id]]]
    [second_processes
      [second_messages [second_globals second_next_id]]].
  repeat split.
  - intros process field.
    rewrite first_processes. apply second_processes.
  - now rewrite first_messages, second_messages.
  - intro field. rewrite first_globals. apply second_globals.
  - now rewrite first_next_id, second_next_id.
Qed.

(** The scheduler-facing event surface is fixed and protocol-neutral.  The
    scheduler may initiate execution or select one queued message.  It cannot
    choose a protocol rule or provide a successor state. *)
Inductive ir_external_event
    (node : Type) (signature : protocol_signature) : Type :=
  | IRProtocolStart :
      ir_start_certificates node signature ->
      ir_external_event node signature
  | IRProtocolDeliver :
      nat ->
      ir_delivery_certificates node signature ->
      ir_external_event node signature.

Arguments IRProtocolStart {node signature} _.
Arguments IRProtocolDeliver {node signature} _ _.

(** Internal evaluation uses a resolved event.  Resolution replaces the
    scheduler-supplied message ID with the authoritative queued message exactly
    once, so later actions may remove that message without losing access to its
    sender, receiver, kind, or payload. *)
Inductive ir_runtime_event
    (node : Type) (signature : protocol_signature) : Type :=
  | IRRuntimeQuery : ir_runtime_event node signature
  | IRRuntimeStart :
      ir_start_certificates node signature ->
      ir_runtime_event node signature
  | IRRuntimeDeliver :
      ir_message node signature ->
      ir_delivery_certificates node signature ->
      ir_runtime_event node signature.

Arguments IRRuntimeStart {node signature} _.
Arguments IRRuntimeDeliver {node signature} _ _.
Arguments IRRuntimeQuery {node signature}.

Definition ir_resolve_event
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (event : ir_external_event node signature) :
    option (ir_runtime_event node signature) :=
  match event with
  | IRProtocolStart certificates => Some (IRRuntimeStart certificates)
  | IRProtocolDeliver selected_id certificates =>
      match ir_find_message selected_id (ir_message_store state) with
      | Some message => Some (IRRuntimeDeliver message certificates)
      | None => None
      end
  end.

(** Dependent update for a typed field map.  The equality proof transports the
    replacement into the selected field's result type; callers never perform a
    runtime cast. *)
Definition ir_update_field
    {node field : Type}
    (field_eq_dec : forall left right : field,
      {left = right} + {left <> right})
    {field_type : field -> ir_type}
    (fields : ir_field_store node field field_type)
    (target : field)
    (value : ir_value node (field_type target)) :
    ir_field_store node field field_type :=
  fun candidate =>
    match field_eq_dec target candidate with
    | left equal =>
        eq_rect target
          (fun selected => ir_value node (field_type selected))
          value candidate equal
    | right _ => fields candidate
    end.

Lemma ir_update_field_same
    {node field : Type}
    (field_eq_dec : forall left right : field,
      {left = right} + {left <> right})
    {field_type : field -> ir_type}
    (fields : ir_field_store node field field_type)
    (target : field)
    (value : ir_value node (field_type target)) :
  ir_update_field field_eq_dec fields target value target = value.
Proof.
  unfold ir_update_field.
  destruct (field_eq_dec target target) as [equal | different].
  - replace equal with (eq_refl target).
    reflexivity.
    apply UIP_dec. exact field_eq_dec.
  - exfalso. apply different. reflexivity.
Qed.

Lemma ir_update_field_different
    {node field : Type}
    (field_eq_dec : forall left right : field,
      {left = right} + {left <> right})
    {field_type : field -> ir_type}
    (fields : ir_field_store node field field_type)
    (target candidate : field)
    (value : ir_value node (field_type target)) :
  target <> candidate ->
  ir_update_field field_eq_dec fields target value candidate =
    fields candidate.
Proof.
  intro different.
  unfold ir_update_field.
  destruct (field_eq_dec target candidate) as [equal | not_equal].
  - contradiction.
  - reflexivity.
Qed.

Definition ir_update_processes
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (processes : node -> ir_local_store node signature)
    (target : node)
    (replacement : ir_local_store node signature) :
    node -> ir_local_store node signature :=
  fun candidate =>
    if node_eq_dec target candidate then replacement else processes candidate.

Lemma ir_update_processes_same
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (processes : node -> ir_local_store node signature)
    (target : node)
    (replacement : ir_local_store node signature) :
  ir_update_processes node_eq_dec processes target replacement target =
    replacement.
Proof.
  unfold ir_update_processes.
  destruct (node_eq_dec target target) as [equal | different].
  - reflexivity.
  - exfalso. apply different. reflexivity.
Qed.

Lemma ir_update_processes_different
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (processes : node -> ir_local_store node signature)
    (target candidate : node)
    (replacement : ir_local_store node signature) :
  target <> candidate ->
  ir_update_processes node_eq_dec processes target replacement candidate =
    processes candidate.
Proof.
  intro different.
  unfold ir_update_processes.
  destruct (node_eq_dec target candidate) as [equal | not_equal].
  - contradiction.
  - reflexivity.
Qed.

(** Two representative state updates exercise both levels of dependent maps:
    a field of one process and a global field. *)
Definition ir_set_local_field
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (state : ir_protocol_state node signature)
    (process : node)
    (field : signature_local_field signature)
    (value : ir_value node (signature_local_field_type signature field)) :
    ir_protocol_state node signature :=
  let replacement :=
    ir_update_field
      (signature_local_field_eq_dec signature)
      (ir_processes state process)
      field value in
  mkIRProtocolState
    (ir_update_processes node_eq_dec (ir_processes state) process replacement)
    (ir_message_store state)
    (ir_global_fields state)
    (ir_next_message_id state).

(** Reading a different local field after a local update observes the old
    value.  Action-correspondence proofs can therefore reason about sequences
    of field updates without unfolding the dependent field store. *)
Lemma ir_set_local_field_read_different
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (state : ir_protocol_state node signature)
    (process : node)
    (updated observed : signature_local_field signature)
    (value : ir_value node
      (signature_local_field_type signature updated)) :
  updated <> observed ->
  ir_processes
      (ir_set_local_field node_eq_dec state process updated value)
      process observed =
    ir_processes state process observed.
Proof.
  intro different.
  unfold ir_set_local_field.
  cbn [ir_processes].
  rewrite ir_update_processes_same.
  now apply ir_update_field_different.
Qed.

(** Updating one process leaves every field of a different process
    unchanged.  Protocol-specific invariant proofs use this observation to
    reason about local writes without unfolding the dependent stores. *)
Lemma ir_set_local_field_read_other_process
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (state : ir_protocol_state node signature)
    (updated_process observed_process : node)
    (field : signature_local_field signature)
    (value : ir_value node
      (signature_local_field_type signature field))
    (observed_field : signature_local_field signature) :
  updated_process <> observed_process ->
  ir_processes
      (ir_set_local_field node_eq_dec state updated_process field value)
      observed_process observed_field =
    ir_processes state observed_process observed_field.
Proof.
  intro different.
  unfold ir_set_local_field.
  cbn [ir_processes].
  now rewrite ir_update_processes_different.
Qed.

Definition ir_set_global_field
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (field : signature_global_field signature)
    (value : ir_value node (signature_global_field_type signature field)) :
    ir_protocol_state node signature :=
  mkIRProtocolState
    (ir_processes state)
    (ir_message_store state)
    (ir_update_field
      (signature_global_field_eq_dec signature)
      (ir_global_fields state)
      field value)
    (ir_next_message_id state).

Theorem ir_set_local_field_same
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (state : ir_protocol_state node signature)
    (process : node)
    (field : signature_local_field signature)
    (value : ir_value node (signature_local_field_type signature field)) :
  ir_processes
    (ir_set_local_field node_eq_dec state process field value)
    process field = value.
Proof.
  change
    (ir_update_processes node_eq_dec (ir_processes state) process
      (ir_update_field
        (signature_local_field_eq_dec signature)
        (ir_processes state process)
        field value)
      process field = value).
  rewrite ir_update_processes_same.
  apply ir_update_field_same.
Qed.

Theorem ir_set_global_field_same
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (field : signature_global_field signature)
    (value : ir_value node (signature_global_field_type signature field)) :
  ir_global_fields (ir_set_global_field state field value) field = value.
Proof.
  change
    (ir_update_field
      (signature_global_field_eq_dec signature)
      (ir_global_fields state)
      field value field = value).
  apply ir_update_field_same.
Qed.
