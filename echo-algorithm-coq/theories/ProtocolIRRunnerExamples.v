(** * Complete non-Echo execution through the generic bounded runner *)

From Stdlib Require Import List Bool Arith String.
Import ListNotations.
Open Scope string_scope.
Require Import ProtocolIRTypes ProtocolIRTypesExamples
  ProtocolIRExpressions ProtocolIRExpressionsExamples
  ProtocolIRActions ProtocolIRActionsExamples
  ProtocolIRInterpreter ProtocolIRInterpreterExamples ProtocolIRRunner.

Definition counter_start_certificates :
    ir_start_certificates nat counter_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_start_certificate_field_type
          counter_signature selected) with
    | CounterStartOrder => IRListNodeValue [0]
    end.

Definition counter_start_payload :
    ir_payload_exprs nat counter_signature :=
  [@mkIRPayloadExprEntry nat counter_signature
      CounterAmount
      (@IRLiteral nat counter_signature IRNat (IRNatValue 5));
   @mkIRPayloadExprEntry nat counter_signature
      CounterCause
      (@IRLiteral nat counter_signature IRMessageRef
        (IRMessageRefValue 0))].

Definition counter_start_action : ir_action nat counter_signature :=
  @IRSequenceAction nat counter_signature
    (@IRSetGlobalAction nat counter_signature CounterStarted
      (@IRLiteral nat counter_signature IRBool (IRBoolValue true)))
    (@IREmitAction nat counter_signature CounterAdd
      (@IRConfigRead nat counter_signature CounterInitiator)
      (@IRConfigRead nat counter_signature CounterInitiator)
      counter_start_payload).

Definition counter_start_rule : ir_rule nat counter_signature :=
  @mkIRRule nat counter_signature
    CounterStartRule
    (@IRStartPattern counter_signature)
    []
    counter_start_action.

Definition counter_complete_expr :
    ir_expr nat counter_signature IRBool :=
  @IRAndExpr nat counter_signature
    (@IREqualExpr nat counter_signature IRNat
      (@IRGlobalRead nat counter_signature CounterTotal)
      (@IRLiteral nat counter_signature IRNat (IRNatValue 5)))
    (@IRMessageStoreEmptyExpr nat counter_signature).

Definition counter_stuck_expr :
    ir_expr nat counter_signature IRBool :=
  @IRAndExpr nat counter_signature
    (@IRGlobalRead nat counter_signature CounterStarted)
    (@IRAndExpr nat counter_signature
      (@IRNotExpr nat counter_signature counter_complete_expr)
      (@IRMessageStoreEmptyExpr nat counter_signature)).

Definition counter_program :
    ir_protocol_program nat counter_signature :=
  @mkIRProtocolProgram nat counter_signature
    1 1 "counter"
    (initial_counter_local 0)
    initial_counter_globals
    1
    [counter_start_rule; counter_add_rule]
    counter_complete_expr
    counter_stuck_expr.

Definition counter_schedule :
    list (ir_external_event nat counter_signature) :=
  [IRProtocolStart counter_start_certificates;
   IRProtocolDeliver 1 counter_delivery_certificates].

Definition counter_run : ir_run_outcome nat counter_signature :=
  run_ir_protocol Nat.eq_dec counter_config counter_program 2 counter_schedule.

Example complete_counter_run_uses_two_steps :
  ir_run_outcome_steps counter_run = 2.
Proof. reflexivity. Qed.

Example complete_counter_run_has_expected_state :
  match counter_run with
  | IRRunComplete state steps =>
      (steps,
       ir_global_fields state CounterTotal,
       List.length (ir_message_store state),
       ir_next_message_id state)
  | _ => (999, IRNatValue 999, 999, 999)
  end =
  (2, IRNatValue 5, 0, 2).
Proof. reflexivity. Qed.

Example zero_fuel_is_bounded_before_start :
  run_ir_protocol Nat.eq_dec counter_config counter_program 0
    counter_schedule =
  IRRunBounded (initialize_ir_protocol counter_program) 0.
Proof. reflexivity. Qed.
