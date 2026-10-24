(** * Non-Echo examples for immutable generic actions *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRTypesExamples
  ProtocolIRExpressions ProtocolIRExpressionsExamples ProtocolIRActions.

Definition counter_accumulate_action :
    ir_action nat counter_signature :=
  @IRSetGlobalAction nat counter_signature CounterTotal
    counter_total_after_message.

Example evaluates_typed_global_update :
  option_map
    (fun state : ir_protocol_state nat counter_signature =>
      ir_global_fields state CounterTotal)
    (eval_ir_action Nat.eq_dec counter_config counter_expression_state
      counter_runtime_delivery_event counter_accumulate_action) =
  Some (IRNatValue 5).
Proof. reflexivity. Qed.

Definition counter_remove_and_reply :
    ir_action nat counter_signature :=
  @IRSequenceAction nat counter_signature
    (@IRRemoveSelectedMessageAction nat counter_signature)
    (@IREmitAction nat counter_signature CounterDone
      (@IRMessageReceiverExpr nat counter_signature)
      (@IRMessageSenderExpr nat counter_signature)
      []).

Definition queued_counter_state :
    ir_protocol_state nat counter_signature :=
  counter_expression_state.

Example sequence_removes_then_emits :
  option_map
    (fun state : ir_protocol_state nat counter_signature =>
      (List.length (ir_message_store state), ir_next_message_id state))
    (eval_ir_action Nat.eq_dec counter_config queued_counter_state
      counter_runtime_delivery_event counter_remove_and_reply) =
  Some (1, 3).
Proof. reflexivity. Qed.

Example emitted_reply_has_deterministic_identity :
  option_map
    (fun state : ir_protocol_state nat counter_signature =>
      List.map
        (fun message : ir_message nat counter_signature =>
          (ir_message_id message,
           ir_message_sender message,
           ir_message_receiver message))
        (ir_message_store state))
    (eval_ir_action Nat.eq_dec counter_config queued_counter_state
      counter_runtime_delivery_event counter_remove_and_reply) =
  Some [(2, 0, 1)].
Proof. reflexivity. Qed.
