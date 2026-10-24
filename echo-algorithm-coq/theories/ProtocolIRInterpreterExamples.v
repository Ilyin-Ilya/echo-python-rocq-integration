(** * Non-Echo examples for generic rule selection and execution *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRTypesExamples
  ProtocolIRExpressions ProtocolIRExpressionsExamples
  ProtocolIRActions ProtocolIRActionsExamples ProtocolIRInterpreter.

Definition counter_receiver_is_initiator :
    ir_expr nat counter_signature IRBool :=
  @IREqualExpr nat counter_signature IRNode
    (@IRMessageReceiverExpr nat counter_signature)
    (@IRConfigRead nat counter_signature CounterInitiator).

Definition counter_add_rule : ir_rule nat counter_signature :=
  @mkIRRule nat counter_signature
    CounterAddRule
    (@IRDeliveryPattern counter_signature CounterAdd)
    [counter_receiver_is_initiator]
    (@IRSequenceAction nat counter_signature
      counter_accumulate_action
      (@IRRemoveSelectedMessageAction nat counter_signature)).

Definition counter_rules : list (ir_rule nat counter_signature) :=
  [counter_add_rule].

Definition counter_step_result :=
  interpret_protocol_rules Nat.eq_dec counter_config counter_rules
    counter_expression_state counter_delivery_event.

Example selected_message_id_is_resolved_from_state :
  ir_resolve_event counter_expression_state counter_delivery_event =
  Some counter_runtime_delivery_event.
Proof. reflexivity. Qed.

Example generic_rule_executes_counter_message :
  match counter_step_result with
  | IRStepSuccess rule successor =>
      (rule,
       ir_global_fields successor CounterTotal,
       List.length (ir_message_store successor))
  | IRStepFailure _ =>
      (CounterStartRule, IRNatValue 999, 999)
  end =
  (CounterAddRule, IRNatValue 5, 0).
Proof. reflexivity. Qed.

Example unqueued_message_is_rejected_before_rule_selection :
  interpret_protocol_rules Nat.eq_dec counter_config counter_rules
    counter_expression_state
    (IRProtocolDeliver 99 counter_delivery_certificates) =
  IRStepFailure IRUnqueuedMessage.
Proof. reflexivity. Qed.

Example duplicate_enabled_rules_are_rejected :
  interpret_protocol_rules Nat.eq_dec counter_config
    [counter_add_rule; counter_add_rule]
    counter_expression_state counter_delivery_event =
  IRStepFailure IRAmbiguousEnabledRules.
Proof. reflexivity. Qed.
