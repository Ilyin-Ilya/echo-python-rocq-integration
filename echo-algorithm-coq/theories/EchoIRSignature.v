(** * Echo identifiers for the protocol-neutral typed IR

    This module declares names and types only.  Echo behavior is represented
    separately as ordinary generic IR data in [EchoIRProgram]. *)

From Stdlib Require Import List Bool Arith.
Require Import ProtocolIRTypes.

Inductive echo_ir_local_field : Type :=
  | EchoIRParent
  | EchoIRPending
  | EchoIRFinished.

Definition echo_ir_local_field_eq_dec
    (left right : echo_ir_local_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_ir_local_field_type
    (field : echo_ir_local_field) : ir_type :=
  match field with
  | EchoIRParent => IROptionNode
  | EchoIRPending => IRListNode
  | EchoIRFinished => IRBool
  end.

Inductive echo_ir_global_field : Type :=
  | EchoIRStarted.

Definition echo_ir_global_field_eq_dec
    (left right : echo_ir_global_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_ir_global_field_type
    (_ : echo_ir_global_field) : ir_type := IRBool.

Inductive echo_ir_config_field : Type :=
  | EchoIRInitiator.

Definition echo_ir_config_field_eq_dec
    (left right : echo_ir_config_field) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_ir_config_field_type
    (_ : echo_ir_config_field) : ir_type := IRNode.

Inductive echo_ir_message_kind : Type :=
  | EchoIRRequest
  | EchoIRReply.

Definition echo_ir_message_kind_eq_dec
    (left right : echo_ir_message_kind) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

(** Echo messages carry no payload.  Keeping the identifier type empty means
    a well-typed Echo IR program cannot accidentally read or emit one. *)
Inductive echo_ir_payload_field : Type := .

Definition echo_ir_payload_field_eq_dec
    (left right : echo_ir_payload_field) : {left = right} + {left <> right}.
Proof. destruct left. Defined.

Definition echo_ir_payload_field_type
    (field : echo_ir_payload_field) : ir_type :=
  match field with end.

Inductive echo_ir_start_certificate_field : Type :=
  | EchoIRStartOrder.

Definition echo_ir_start_certificate_field_eq_dec
    (left right : echo_ir_start_certificate_field) :
    {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_ir_start_certificate_field_type
    (_ : echo_ir_start_certificate_field) : ir_type := IRListNode.

(** Delivery certificates replace the branch-specific data formerly carried
    by Echo event constructors.  Rules decide whether a field is relevant. *)
Inductive echo_ir_delivery_certificate_field : Type :=
  | EchoIRForwardOrder
  | EchoIRExpectedParent.

Definition echo_ir_delivery_certificate_field_eq_dec
    (left right : echo_ir_delivery_certificate_field) :
    {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_ir_delivery_certificate_field_type
    (field : echo_ir_delivery_certificate_field) : ir_type :=
  match field with
  | EchoIRForwardOrder => IRListNode
  | EchoIRExpectedParent => IRNode
  end.

Inductive echo_ir_rule_id : Type :=
  | EchoIRStartRule
  | EchoIRFirstRequestNonLeafRule
  | EchoIRFirstRequestLeafRule
  | EchoIRRepeatedRequestRule
  | EchoIRInitiatorRequestRule
  | EchoIRParticipantReplyMoreRule
  | EchoIRParticipantReplyFinalRule
  | EchoIRInitiatorReplyMoreRule
  | EchoIRInitiatorReplyFinalRule.

Definition echo_ir_rule_id_eq_dec
    (left right : echo_ir_rule_id) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_ir_signature : protocol_signature :=
  mkProtocolSignature
    echo_ir_local_field
    echo_ir_local_field_eq_dec
    echo_ir_local_field_type
    echo_ir_global_field
    echo_ir_global_field_eq_dec
    echo_ir_global_field_type
    echo_ir_config_field
    echo_ir_config_field_eq_dec
    echo_ir_config_field_type
    echo_ir_message_kind
    echo_ir_message_kind_eq_dec
    echo_ir_payload_field
    echo_ir_payload_field_eq_dec
    echo_ir_payload_field_type
    echo_ir_start_certificate_field
    echo_ir_start_certificate_field_eq_dec
    echo_ir_start_certificate_field_type
    echo_ir_delivery_certificate_field
    echo_ir_delivery_certificate_field_eq_dec
    echo_ir_delivery_certificate_field_type
    echo_ir_rule_id
    echo_ir_rule_id_eq_dec.
