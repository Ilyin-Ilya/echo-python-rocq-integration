(** * Maintained generic-IR conformance fixtures for cross-language execution

    These are ordinary inputs and computed results of the one generic Echo
    interpreter.  They contain no alternate transition relation. *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature
  EchoIRExecutable.

Definition echo_conformance_config_fields :
    ir_config_store nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_config_field_type echo_ir_signature selected) with
    | EchoIRInitiator => IRNodeValue 0
    end.

Definition echo_conformance_config :
    ir_protocol_config nat echo_ir_signature :=
  mkIRProtocolConfig
    [0; 1]
    (fun owner => if Nat.eq_dec owner 0 then [1] else [0])
    echo_conformance_config_fields.

Definition echo_conformance_start_certificates :
    ir_start_certificates nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_start_certificate_field_type echo_ir_signature selected) with
    | EchoIRStartOrder => IRListNodeValue [1]
    end.

Definition echo_conformance_delivery_certificates :
    ir_delivery_certificates nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_delivery_certificate_field_type
          echo_ir_signature selected) with
    | EchoIRForwardOrder => IRListNodeValue []
    | EchoIRExpectedParent => IRNodeValue 0
    end.

Definition echo_conformance_start_event :
    ir_external_event nat echo_ir_signature :=
  IRProtocolStart echo_conformance_start_certificates.

Definition echo_conformance_schedule :
    list (ir_external_event nat echo_ir_signature) :=
  [echo_conformance_start_event;
   IRProtocolDeliver 1 echo_conformance_delivery_certificates;
   IRProtocolDeliver 2 echo_conformance_delivery_certificates].

Definition echo_conformance_initial_state :
    ir_protocol_state nat echo_ir_signature :=
  @echo_initial_state nat.

Definition echo_conformance_start_result :
    ir_step_result nat echo_ir_signature :=
  echo_exec nat Nat.eq_dec echo_conformance_config
    echo_conformance_initial_state echo_conformance_start_event.

Definition echo_conformance_run_result :
    ir_run_outcome nat echo_ir_signature :=
  echo_run nat Nat.eq_dec echo_conformance_config 3
    echo_conformance_schedule.

(** A five-node branch fixture covers all nine Echo rules without referring to
    the historical Echo-specific executable types. *)
Definition echo_conformance_branch_neighbors (owner : nat) : list nat :=
  match owner with
  | 0 => [1; 2]
  | 1 => [0; 3; 4]
  | 2 => [0]
  | 3 => [1]
  | 4 => [1]
  | _ => []
  end.

Definition echo_conformance_branch_config :
    ir_protocol_config nat echo_ir_signature :=
  mkIRProtocolConfig [0; 1; 2; 3; 4]
    echo_conformance_branch_neighbors echo_conformance_config_fields.

Definition echo_conformance_process
    (parent : option nat) (pending : list nat) (finished : bool) :
    ir_local_store nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_local_field_type echo_ir_signature selected) with
    | EchoIRParent => IROptionNodeValue parent
    | EchoIRPending => IRListNodeValue pending
    | EchoIRFinished => IRBoolValue finished
    end.

Definition echo_conformance_initial_process :
    ir_local_store nat echo_ir_signature :=
  echo_conformance_process None [] false.

Definition echo_conformance_started_globals :
    ir_global_store nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_global_field_type echo_ir_signature selected) with
    | EchoIRStarted => IRBoolValue true
    end.

Definition echo_conformance_message
    (kind : echo_ir_message_kind) (sender receiver : nat) :
    ir_message nat echo_ir_signature :=
  @mkIRMessage nat echo_ir_signature 1 kind sender receiver [].

Definition echo_conformance_single_process_state
    (target : nat) (process : ir_local_store nat echo_ir_signature)
    (message : ir_message nat echo_ir_signature) :
    ir_protocol_state nat echo_ir_signature :=
  mkIRProtocolState
    (fun owner =>
      if Nat.eq_dec owner target then process
      else echo_conformance_initial_process)
    [message]
    echo_conformance_started_globals
    2.

Definition echo_conformance_delivery_certificates_for
    (forwards : list nat) (expected_parent : nat) :
    ir_delivery_certificates nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_delivery_certificate_field_type
          echo_ir_signature selected) with
    | EchoIRForwardOrder => IRListNodeValue forwards
    | EchoIRExpectedParent => IRNodeValue expected_parent
    end.

Definition echo_conformance_delivery_event
    (forwards : list nat) (expected_parent : nat) :
    ir_external_event nat echo_ir_signature :=
  IRProtocolDeliver 1
    (echo_conformance_delivery_certificates_for forwards expected_parent).

Record echo_ir_step_fixture : Type := mkEchoIRStepFixture {
  echo_ir_step_fixture_rule : echo_ir_rule_id;
  echo_ir_step_fixture_state : ir_protocol_state nat echo_ir_signature;
  echo_ir_step_fixture_event : ir_external_event nat echo_ir_signature
}.

Definition echo_ir_step_fixture_result
    (fixture : echo_ir_step_fixture) :
    ir_step_result nat echo_ir_signature :=
  echo_exec nat Nat.eq_dec echo_conformance_branch_config
    (echo_ir_step_fixture_state fixture)
    (echo_ir_step_fixture_event fixture).

Definition echo_conformance_step_fixtures : list echo_ir_step_fixture :=
  [mkEchoIRStepFixture
     EchoIRStartRule (@echo_initial_state nat)
     (IRProtocolStart
       (fun field =>
         match field as selected
           return ir_value nat
             (signature_start_certificate_field_type
               echo_ir_signature selected) with
         | EchoIRStartOrder => IRListNodeValue [1; 2]
         end));
   mkEchoIRStepFixture
     EchoIRFirstRequestNonLeafRule
     (echo_conformance_single_process_state 1
       echo_conformance_initial_process
       (echo_conformance_message EchoIRRequest 0 1))
     (echo_conformance_delivery_event [3; 4] 0);
   mkEchoIRStepFixture
     EchoIRFirstRequestLeafRule
     (echo_conformance_single_process_state 2
       echo_conformance_initial_process
       (echo_conformance_message EchoIRRequest 0 2))
     (echo_conformance_delivery_event [] 0);
   mkEchoIRStepFixture
     EchoIRRepeatedRequestRule
     (echo_conformance_single_process_state 1
       (echo_conformance_process (Some 0) [3; 4] false)
       (echo_conformance_message EchoIRRequest 3 1))
     (echo_conformance_delivery_event [] 0);
   mkEchoIRStepFixture
     EchoIRInitiatorRequestRule
     (echo_conformance_single_process_state 0
       (echo_conformance_process None [1; 2] false)
       (echo_conformance_message EchoIRRequest 1 0))
     (echo_conformance_delivery_event [] 0);
   mkEchoIRStepFixture
     EchoIRParticipantReplyMoreRule
     (echo_conformance_single_process_state 1
       (echo_conformance_process (Some 0) [3; 4] false)
       (echo_conformance_message EchoIRReply 3 1))
     (echo_conformance_delivery_event [] 0);
   mkEchoIRStepFixture
     EchoIRParticipantReplyFinalRule
     (echo_conformance_single_process_state 1
       (echo_conformance_process (Some 0) [3] false)
       (echo_conformance_message EchoIRReply 3 1))
     (echo_conformance_delivery_event [] 0);
   mkEchoIRStepFixture
     EchoIRInitiatorReplyMoreRule
     (echo_conformance_single_process_state 0
       (echo_conformance_process None [1; 2] false)
       (echo_conformance_message EchoIRReply 1 0))
     (echo_conformance_delivery_event [] 0);
   mkEchoIRStepFixture
     EchoIRInitiatorReplyFinalRule
     (echo_conformance_single_process_state 0
       (echo_conformance_process None [1] false)
       (echo_conformance_message EchoIRReply 1 0))
     (echo_conformance_delivery_event [] 0)].

Example echo_conformance_start_selects_start_rule :
  exists successor,
    echo_conformance_start_result =
      @IRStepSuccess nat echo_ir_signature EchoIRStartRule successor.
Proof. eexists. vm_compute. reflexivity. Qed.

Example echo_conformance_two_node_run_completes :
  exists final_state,
    echo_conformance_run_result =
      @IRRunComplete nat echo_ir_signature final_state 3.
Proof. eexists. vm_compute. reflexivity. Qed.

Example echo_conformance_has_nine_step_fixtures :
  List.length echo_conformance_step_fixtures = 9.
Proof. reflexivity. Qed.
