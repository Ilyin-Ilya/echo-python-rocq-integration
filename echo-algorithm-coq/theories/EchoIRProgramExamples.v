(** * Concrete old/new agreement checks for all generic Echo rules

    These examples run the generic rule selector, not a chosen rule tag.  The
    finite observation records every configured process, queued message,
    global flag, and next message identifier. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR EchoExecutableExamples
  ProtocolIRTypes ProtocolIRInterpreter EchoIRSignature EchoIRProgram
  EchoIRCompatibility.

Definition echo_ir_process_view : Type :=
  (option nat * list nat * bool)%type.

Definition echo_ir_message_view : Type :=
  (nat * echo_ir_message_kind * nat * nat)%type.

Definition echo_ir_state_view : Type :=
  (list (nat * echo_ir_process_view) *
   list echo_ir_message_view * bool * nat)%type.

Definition observe_echo_ir_process
    (state : ir_protocol_state nat echo_ir_signature)
    (process : nat) : echo_ir_process_view :=
  match ir_processes state process EchoIRParent,
        ir_processes state process EchoIRPending,
        ir_processes state process EchoIRFinished with
  | IROptionNodeValue parent,
    IRListNodeValue pending,
    IRBoolValue finished => (parent, pending, finished)
  end.

Definition observe_echo_ir_message
    (message : ir_message nat echo_ir_signature) : echo_ir_message_view :=
  (ir_message_id message,
   ir_message_kind message,
   ir_message_sender message,
   ir_message_receiver message).

Definition observe_echo_ir_state
    (state : ir_protocol_state nat echo_ir_signature) : echo_ir_state_view :=
  (List.map
    (fun process => (process, observe_echo_ir_process state process))
    executable_example_nodes,
   List.map observe_echo_ir_message (ir_message_store state),
   match ir_global_fields state EchoIRStarted with
   | IRBoolValue value => value
   end,
   ir_next_message_id state).

Definition observe_generic_echo_step
    (state : @executable_echo_state nat)
    (event : @echo_event nat) :
    option (echo_ir_rule_id * echo_ir_state_view) :=
  match interpret_protocol_rules
    Nat.eq_dec
    (echo_ir_encode_config executable_example_config)
    (@echo_ir_rules nat)
    (echo_ir_encode_state state)
    (echo_ir_encode_event executable_example_config event) with
  | IRStepSuccess rule successor =>
      Some (rule, observe_echo_ir_state successor)
  | IRStepFailure _ => None
  end.

Definition observe_old_echo_step
    (rule : echo_ir_rule_id)
    (state : @executable_echo_state nat)
    (event : @echo_event nat) :
    option (echo_ir_rule_id * echo_ir_state_view) :=
  match @echo_exec nat Nat.eq_dec executable_example_config state event with
  | Some successor =>
      Some (rule, observe_echo_ir_state (echo_ir_encode_state successor))
  | None => None
  end.

Example generic_start_matches_current_echo :
  observe_generic_echo_step executable_example_initial (EchoStart [1; 2]) =
  observe_old_echo_step EchoIRStartRule
    executable_example_initial (EchoStart [1; 2]).
Proof. vm_compute. reflexivity. Qed.

Example generic_first_nonleaf_matches_current_echo :
  observe_generic_echo_step first_nonleaf_state
    (EchoFirstRequestNonLeaf first_nonleaf_message [3; 4]) =
  observe_old_echo_step EchoIRFirstRequestNonLeafRule first_nonleaf_state
    (EchoFirstRequestNonLeaf first_nonleaf_message [3; 4]).
Proof. vm_compute. reflexivity. Qed.

Example generic_first_leaf_matches_current_echo :
  observe_generic_echo_step first_leaf_state
    (EchoFirstRequestLeaf first_leaf_message) =
  observe_old_echo_step EchoIRFirstRequestLeafRule first_leaf_state
    (EchoFirstRequestLeaf first_leaf_message).
Proof. vm_compute. reflexivity. Qed.

Example generic_repeated_request_matches_current_echo :
  observe_generic_echo_step repeated_echo_state
    (EchoRepeatedRequest repeated_echo_message) =
  observe_old_echo_step EchoIRRepeatedRequestRule repeated_echo_state
    (EchoRepeatedRequest repeated_echo_message).
Proof. vm_compute. reflexivity. Qed.

Example generic_initiator_request_matches_current_echo :
  observe_generic_echo_step initiator_echo_state
    (EchoInitiatorRequest initiator_echo_message) =
  observe_old_echo_step EchoIRInitiatorRequestRule initiator_echo_state
    (EchoInitiatorRequest initiator_echo_message).
Proof. vm_compute. reflexivity. Qed.

Example generic_participant_reply_more_matches_current_echo :
  observe_generic_echo_step participant_ack_more_state
    (EchoParticipantReplyMore participant_ack_more_message 0) =
  observe_old_echo_step EchoIRParticipantReplyMoreRule
    participant_ack_more_state
    (EchoParticipantReplyMore participant_ack_more_message 0).
Proof. vm_compute. reflexivity. Qed.

Example generic_participant_reply_final_matches_current_echo :
  observe_generic_echo_step participant_ack_final_state
    (EchoParticipantReplyFinal participant_ack_final_message 0) =
  observe_old_echo_step EchoIRParticipantReplyFinalRule
    participant_ack_final_state
    (EchoParticipantReplyFinal participant_ack_final_message 0).
Proof. vm_compute. reflexivity. Qed.

Example generic_initiator_reply_more_matches_current_echo :
  observe_generic_echo_step initiator_ack_more_state
    (EchoInitiatorReplyMore initiator_ack_more_message) =
  observe_old_echo_step EchoIRInitiatorReplyMoreRule
    initiator_ack_more_state
    (EchoInitiatorReplyMore initiator_ack_more_message).
Proof. vm_compute. reflexivity. Qed.

Example generic_initiator_reply_final_matches_current_echo :
  observe_generic_echo_step initiator_ack_final_state
    (EchoInitiatorReplyFinal initiator_ack_final_message) =
  observe_old_echo_step EchoIRInitiatorReplyFinalRule
    initiator_ack_final_state
    (EchoInitiatorReplyFinal initiator_ack_final_message).
Proof. vm_compute. reflexivity. Qed.

Example generic_echo_rejects_invalid_forward_order :
  observe_generic_echo_step first_nonleaf_state
    (EchoFirstRequestNonLeaf first_nonleaf_message [3]) = None.
Proof. vm_compute. reflexivity. Qed.
