(** * Non-Echo examples for typed expression evaluation *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRTypesExamples ProtocolIRExpressions.

Definition counter_payload : ir_payload_store nat counter_signature :=
  [@mkIRPayloadEntry nat counter_signature
      CounterAmount (IRNatValue 5);
   @mkIRPayloadEntry nat counter_signature
      CounterCause (IRMessageRefValue 0)].

Definition counter_message : ir_message nat counter_signature :=
  @mkIRMessage nat counter_signature 1 CounterAdd 1 0 counter_payload.

Definition counter_delivery_certificates :
    ir_delivery_certificates nat counter_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_delivery_certificate_field_type
          counter_signature selected) with
    | CounterExpectedParent => IROptionNodeValue (Some 1)
    end.

Definition counter_delivery_event :
    ir_external_event nat counter_signature :=
  IRProtocolDeliver 1 counter_delivery_certificates.

Definition counter_runtime_delivery_event :
    ir_runtime_event nat counter_signature :=
  IRRuntimeDeliver counter_message counter_delivery_certificates.

Definition counter_expression_state :
    ir_protocol_state nat counter_signature :=
  mkIRProtocolState initial_counter_local [counter_message]
    initial_counter_globals 2.

Definition counter_total_after_message :
    ir_expr nat counter_signature IRNat :=
  @IRNatAddExpr nat counter_signature
    (@IRGlobalRead nat counter_signature CounterTotal)
    (@IRPayloadRead nat counter_signature CounterAmount).

Example evaluates_config_read :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    counter_runtime_delivery_event
    (@IRConfigRead nat counter_signature CounterInitiator) =
  Some (IRNodeValue 0).
Proof. reflexivity. Qed.

Example evaluates_topology_neighbors :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    counter_runtime_delivery_event
    (@IRNeighborsExpr nat counter_signature
      (@IRLiteral nat counter_signature IRNode (IRNodeValue 1))) =
  Some (IRListNodeValue [0; 2]).
Proof. reflexivity. Qed.

Example evaluates_message_payload_arithmetic :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    counter_runtime_delivery_event counter_total_after_message =
  Some (IRNatValue 5).
Proof. reflexivity. Qed.

Example rejects_delivery_data_during_startup :
  let start_certificates : ir_start_certificates nat counter_signature :=
    fun field =>
      match field as selected
        return ir_value nat
          (signature_start_certificate_field_type
            counter_signature selected) with
      | CounterStartOrder => IRListNodeValue [1]
      end in
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    (IRRuntimeStart start_certificates)
    (@IRPayloadRead nat counter_signature CounterAmount) = None.
Proof. reflexivity. Qed.

Example constructs_typed_optional_node :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    IRRuntimeQuery
    (@IROptionSomeExpr nat counter_signature
      (@IRLiteral nat counter_signature IRNode (IRNodeValue 2))) =
  Some (IROptionNodeValue (Some 2)).
Proof. reflexivity. Qed.

Example validates_order_certificate_as_permutation :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    IRRuntimeQuery
    (@IRListPermutationExpr nat counter_signature
      (@IRLiteral nat counter_signature IRListNode
        (IRListNodeValue [0; 1; 0]))
      (@IRLiteral nat counter_signature IRListNode
        (IRListNodeValue [0; 0; 1]))) =
  Some (IRBoolValue true).
Proof. reflexivity. Qed.

Example permutation_preserves_duplicate_multiplicity :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    IRRuntimeQuery
    (@IRListPermutationExpr nat counter_signature
      (@IRLiteral nat counter_signature IRListNode
        (IRListNodeValue [0; 1]))
      (@IRLiteral nat counter_signature IRListNode
        (IRListNodeValue [0; 0; 1]))) =
  Some (IRBoolValue false).
Proof. reflexivity. Qed.

Example checks_a_local_field_for_every_configured_node :
  eval_ir_expr Nat.eq_dec counter_config counter_expression_state
    IRRuntimeQuery
    (@IRAllNodesLocalEqualExpr nat counter_signature CounterSeen
      (@IRLiteral nat counter_signature IRBool (IRBoolValue false))) =
  Some (IRBoolValue true).
Proof. reflexivity. Qed.

Example detects_a_noninitial_configured_process :
  eval_ir_expr Nat.eq_dec counter_config
    (ir_set_local_field Nat.eq_dec counter_expression_state
      2 CounterSeen (IRBoolValue true))
    IRRuntimeQuery
    (@IRAllNodesLocalEqualExpr nat counter_signature CounterSeen
      (@IRLiteral nat counter_signature IRBool (IRBoolValue false))) =
  Some (IRBoolValue false).
Proof. reflexivity. Qed.
