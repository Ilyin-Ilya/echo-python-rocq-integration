(** * Canonical generic-IR export of the Echo program *)

From Stdlib Require Import List String Arith DecimalString.
Import ListNotations.
Open Scope string_scope.
Require Import ProtocolIRTypes ProtocolIRRunner ProtocolIRExport EchoIRSignature
  EchoIRProgram EchoIRExecutable EchoIRConformance.

Definition echo_ir_node_atom (node : nat) : string :=
  NilEmpty.string_of_uint (Nat.to_uint node).

Definition echo_ir_local_field_atom (field : echo_ir_local_field) : string :=
  match field with
  | EchoIRParent => "parent"
  | EchoIRPending => "pending"
  | EchoIRFinished => "finished"
  end.

Definition echo_ir_global_field_atom
    (_ : echo_ir_global_field) : string := "started".

Definition echo_ir_config_field_atom
    (_ : echo_ir_config_field) : string := "initiator".

Definition echo_ir_message_kind_atom
    (kind : echo_ir_message_kind) : string :=
  match kind with
  | EchoIRRequest => "request"
  | EchoIRReply => "reply"
  end.

Definition echo_ir_payload_field_atom
    (field : echo_ir_payload_field) : string :=
  match field with end.

Definition echo_ir_start_certificate_field_atom
    (_ : echo_ir_start_certificate_field) : string := "ordered-neighbors".

Definition echo_ir_delivery_certificate_field_atom
    (field : echo_ir_delivery_certificate_field) : string :=
  match field with
  | EchoIRForwardOrder => "ordered-forwards"
  | EchoIRExpectedParent => "expected-parent"
  end.

Definition echo_ir_rule_id_atom (rule : echo_ir_rule_id) : string :=
  match rule with
  | EchoIRStartRule => "start"
  | EchoIRFirstRequestNonLeafRule => "first-request-nonleaf"
  | EchoIRFirstRequestLeafRule => "first-request-leaf"
  | EchoIRRepeatedRequestRule => "repeated-request"
  | EchoIRInitiatorRequestRule => "initiator-request"
  | EchoIRParticipantReplyMoreRule => "participant-reply-more"
  | EchoIRParticipantReplyFinalRule => "participant-reply-final"
  | EchoIRInitiatorReplyMoreRule => "initiator-reply-more"
  | EchoIRInitiatorReplyFinalRule => "initiator-reply-final"
  end.

Definition echo_ir_export_descriptor :
    ir_export_descriptor nat echo_ir_signature :=
  @mkIRExportDescriptor nat echo_ir_signature
    echo_ir_node_atom
    [EchoIRParent; EchoIRPending; EchoIRFinished]
    echo_ir_local_field_atom
    [EchoIRStarted]
    echo_ir_global_field_atom
    [EchoIRInitiator]
    echo_ir_config_field_atom
    [EchoIRRequest; EchoIRReply]
    echo_ir_message_kind_atom
    []
    echo_ir_payload_field_atom
    []
    echo_ir_start_certificate_field_atom
    []
    echo_ir_delivery_certificate_field_atom
    [EchoIRStartRule;
     EchoIRFirstRequestNonLeafRule;
     EchoIRFirstRequestLeafRule;
     EchoIRRepeatedRequestRule;
     EchoIRInitiatorRequestRule;
     EchoIRParticipantReplyMoreRule;
     EchoIRParticipantReplyFinalRule;
     EchoIRInitiatorReplyMoreRule;
     EchoIRInitiatorReplyFinalRule]
    echo_ir_rule_id_atom.

Definition echo_ir_program_sexpr : string :=
  ir_protocol_envelope_sexpr echo_ir_export_descriptor
    (@echo_program nat).

Fixpoint echo_ir_conformance_steps_body
    (fixtures : list echo_ir_step_fixture) : string :=
  match fixtures with
  | [] => ""
  | fixture :: rest =>
      " (step " ++
        echo_ir_rule_id_atom (echo_ir_step_fixture_rule fixture) ++ " " ++
        ir_config_sexpr echo_ir_export_descriptor
          echo_conformance_branch_config ++ " " ++
        ir_state_sexpr echo_ir_export_descriptor [0; 1; 2; 3; 4]
          (echo_ir_step_fixture_state fixture) ++ " " ++
        ir_external_event_sexpr echo_ir_export_descriptor
          (echo_ir_step_fixture_event fixture) ++ " " ++
        ir_step_result_sexpr echo_ir_export_descriptor [0; 1; 2; 3; 4]
          (echo_ir_step_fixture_result fixture) ++ ")" ++
        echo_ir_conformance_steps_body rest
  end.

Definition echo_ir_conformance_sexpr : string :=
  "(echo-conformance " ++
    "(steps" ++
      echo_ir_conformance_steps_body echo_conformance_step_fixtures ++ ") " ++
    "(runs (run two-node-complete " ++
        ir_config_sexpr echo_ir_export_descriptor echo_conformance_config ++ " " ++
        ir_nat_atom 3 ++ " " ++
        ir_external_events_sexpr echo_ir_export_descriptor
          echo_conformance_schedule ++ " " ++
        ir_run_outcome_sexpr echo_ir_export_descriptor [0; 1]
          echo_conformance_run_result ++ ")))".

Example echo_ir_export_contains_nine_rules :
  List.length (ir_program_rules (@echo_program nat)) = 9.
Proof. reflexivity. Qed.

Example echo_ir_conformance_export_is_nonempty :
  echo_ir_conformance_sexpr <> "".
Proof. unfold echo_ir_conformance_sexpr. discriminate. Qed.
