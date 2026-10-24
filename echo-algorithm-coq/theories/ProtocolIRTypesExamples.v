(** * Protocol-neutral examples for the typed IR state layer

    This fixture is intentionally not Echo.  It uses a natural-number global
    field and message payload so the first generic layer cannot silently depend
    on Echo's Boolean/parent/pending shape. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes.

Inductive counter_local_field : Type :=
  | CounterSeen
  | CounterParent.

Definition counter_local_field_eq_dec
    (left right : counter_local_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_local_field_type (field : counter_local_field) : ir_type :=
  match field with
  | CounterSeen => IRBool
  | CounterParent => IROptionNode
  end.

Inductive counter_global_field : Type :=
  | CounterStarted
  | CounterTotal.

Definition counter_global_field_eq_dec
    (left right : counter_global_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_global_field_type (field : counter_global_field) : ir_type :=
  match field with
  | CounterStarted => IRBool
  | CounterTotal => IRNat
  end.

Inductive counter_config_field : Type :=
  | CounterInitiator.

Definition counter_config_field_eq_dec
    (left right : counter_config_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_config_field_type
    (_ : counter_config_field) : ir_type := IRNode.

Inductive counter_message_kind : Type :=
  | CounterAdd
  | CounterDone.

Definition counter_message_kind_eq_dec
    (left right : counter_message_kind) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Inductive counter_payload_field : Type :=
  | CounterAmount
  | CounterCause.

Definition counter_payload_field_eq_dec
    (left right : counter_payload_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_payload_field_type
    (field : counter_payload_field) : ir_type :=
  match field with
  | CounterAmount => IRNat
  | CounterCause => IRMessageRef
  end.

Inductive counter_start_certificate_field : Type :=
  | CounterStartOrder.

Definition counter_start_certificate_field_eq_dec
    (left right : counter_start_certificate_field) :
    {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_start_certificate_field_type
    (_ : counter_start_certificate_field) : ir_type := IRListNode.

Inductive counter_delivery_certificate_field : Type :=
  | CounterExpectedParent.

Definition counter_delivery_certificate_field_eq_dec
    (left right : counter_delivery_certificate_field) :
    {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_delivery_certificate_field_type
    (_ : counter_delivery_certificate_field) : ir_type := IROptionNode.

Inductive counter_rule_id : Type :=
  | CounterStartRule
  | CounterAddRule
  | CounterDoneRule.

Definition counter_rule_id_eq_dec
    (left right : counter_rule_id) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition counter_signature : protocol_signature :=
  mkProtocolSignature
    counter_local_field
    counter_local_field_eq_dec
    counter_local_field_type
    counter_global_field
    counter_global_field_eq_dec
    counter_global_field_type
    counter_config_field
    counter_config_field_eq_dec
    counter_config_field_type
    counter_message_kind
    counter_message_kind_eq_dec
    counter_payload_field
    counter_payload_field_eq_dec
    counter_payload_field_type
    counter_start_certificate_field
    counter_start_certificate_field_eq_dec
    counter_start_certificate_field_type
    counter_delivery_certificate_field
    counter_delivery_certificate_field_eq_dec
    counter_delivery_certificate_field_type
    counter_rule_id
    counter_rule_id_eq_dec.

Definition counter_config_fields :
    ir_config_store nat counter_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_config_field_type counter_signature selected) with
    | CounterInitiator => IRNodeValue 0
    end.

Definition counter_neighbors (node : nat) : list nat :=
  match node with
  | 0 => [1]
  | 1 => [0; 2]
  | 2 => [1]
  | _ => []
  end.

Definition counter_config : ir_protocol_config nat counter_signature :=
  mkIRProtocolConfig [0; 1; 2] counter_neighbors counter_config_fields.

Definition initial_counter_local
    (node : nat) : ir_local_store nat counter_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_local_field_type counter_signature selected) with
    | CounterSeen => IRBoolValue false
    | CounterParent => IROptionNodeValue None
    end.

Definition initial_counter_globals :
    ir_global_store nat counter_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_global_field_type counter_signature selected) with
    | CounterStarted => IRBoolValue false
    | CounterTotal => IRNatValue 0
    end.

Definition initial_counter_state :
    ir_protocol_state nat counter_signature :=
  mkIRProtocolState initial_counter_local [] initial_counter_globals 1.

Example local_boolean_update_is_typed :
  ir_processes
    (ir_set_local_field Nat.eq_dec initial_counter_state
      2 CounterSeen (IRBoolValue true))
    2 CounterSeen = IRBoolValue true.
Proof.
  apply ir_set_local_field_same.
Qed.

Example local_update_preserves_another_process :
  ir_processes
    (ir_set_local_field Nat.eq_dec initial_counter_state
      2 CounterSeen (IRBoolValue true))
    3 CounterSeen = IRBoolValue false.
Proof.
  reflexivity.
Qed.

Example global_natural_update_is_typed :
  ir_global_fields
    (ir_set_global_field initial_counter_state
      CounterTotal (IRNatValue 7))
    CounterTotal = IRNatValue 7.
Proof.
  apply ir_set_global_field_same.
Qed.

Example global_update_preserves_local_state :
  ir_processes
    (ir_set_global_field initial_counter_state
      CounterTotal (IRNatValue 7))
    4 CounterSeen = IRBoolValue false.
Proof.
  reflexivity.
Qed.
