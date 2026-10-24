(** * Versioned export of the non-protocol-specific counter fixture *)

From Stdlib Require Import List String Arith DecimalString.
Import ListNotations.
Open Scope string_scope.
Require Import ProtocolIRTypes ProtocolIRTypesExamples
  ProtocolIRExpressions ProtocolIRExpressionsExamples
  ProtocolIRActions ProtocolIRActionsExamples
  ProtocolIRInterpreter ProtocolIRInterpreterExamples
  ProtocolIRRunner ProtocolIRRunnerExamples ProtocolIRExport.

Definition counter_node_atom (node : nat) : string :=
  NilEmpty.string_of_uint (Nat.to_uint node).

Definition counter_local_field_atom (field : counter_local_field) : string :=
  match field with
  | CounterSeen => "seen"
  | CounterParent => "parent"
  end.

Definition counter_global_field_atom
    (field : counter_global_field) : string :=
  match field with
  | CounterStarted => "started"
  | CounterTotal => "total"
  end.

Definition counter_config_field_atom
    (_ : counter_config_field) : string := "initiator".

Definition counter_message_kind_atom
    (kind : counter_message_kind) : string :=
  match kind with
  | CounterAdd => "add"
  | CounterDone => "done"
  end.

Definition counter_payload_field_atom
    (field : counter_payload_field) : string :=
  match field with
  | CounterAmount => "amount"
  | CounterCause => "cause"
  end.

Definition counter_start_certificate_field_atom
    (_ : counter_start_certificate_field) : string := "start-order".

Definition counter_delivery_certificate_field_atom
    (_ : counter_delivery_certificate_field) : string := "expected-parent".

Definition counter_rule_id_atom (rule : counter_rule_id) : string :=
  match rule with
  | CounterStartRule => "start"
  | CounterAddRule => "add"
  | CounterDoneRule => "done"
  end.

Definition counter_export_descriptor :
    ir_export_descriptor nat counter_signature :=
  @mkIRExportDescriptor nat counter_signature
    counter_node_atom
    [CounterSeen; CounterParent]
    counter_local_field_atom
    [CounterStarted; CounterTotal]
    counter_global_field_atom
    [CounterInitiator]
    counter_config_field_atom
    [CounterAdd; CounterDone]
    counter_message_kind_atom
    [CounterAmount; CounterCause]
    counter_payload_field_atom
    [CounterStartOrder]
    counter_start_certificate_field_atom
    [CounterExpectedParent]
    counter_delivery_certificate_field_atom
    [CounterStartRule; CounterAddRule; CounterDoneRule]
    counter_rule_id_atom.

Definition counter_program_sexpr : string :=
  ir_protocol_envelope_sexpr counter_export_descriptor counter_program.

Definition counter_initial_state_sexpr : string :=
  ir_state_sexpr counter_export_descriptor [0; 1]
    (initialize_ir_protocol counter_program).

Definition counter_complete_run_sexpr : string :=
  ir_run_outcome_sexpr counter_export_descriptor [0; 1]
    counter_run.

Example counter_export_versions_are_formal_program_data :
  ir_program_schema_version counter_program = 1 /\
  ir_program_ir_version counter_program = 1 /\
  ir_program_id counter_program = "counter".
Proof. repeat split; reflexivity. Qed.

Example counter_runtime_exports_are_nonempty :
  counter_initial_state_sexpr <> "" /\
  counter_complete_run_sexpr <> "".
Proof. vm_compute. split; discriminate. Qed.
