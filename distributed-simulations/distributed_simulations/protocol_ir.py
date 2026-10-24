"""Compatibility facade for the protocol-neutral reference interpreter.

New production code imports immutable runtime data from ``protocol_values``
and syntax definitions from ``protocol_ir_ast``; export tooling imports
``protocol_ir_codec``.  The facade re-exports those public names while the
split modules remain the preferred imports.  It contains no implementation or
Echo rules.
"""

from __future__ import annotations

from .protocol_ir_codec import (
    decode_exported_config,
    decode_exported_event,
    decode_exported_state,
    decode_ir_capability_manifest,
    decode_protocol_program,
    encode_exported_event,
    encode_exported_run_outcome,
    encode_exported_state,
    encode_exported_step_result,
    encode_exported_value,
)
from .protocol_ir_interpreter import (
    evaluate_action,
    evaluate_expression,
    evaluate_state_predicate,
    initialize_protocol,
    interpret_step,
    make_config,
    make_delivery_event,
    make_start_event,
    run_callback,
    run_schedule,
    runtime_contract,
)
from .protocol_ir_ast import (
    Action,
    EventPattern,
    Expression,
    IRCapabilityManifest,
    ProtocolProgram,
    ProtocolSignature,
    Rule,
    RuntimeContract,
    SUPPORTED_ACTION_CONSTRUCTORS,
    SUPPORTED_EVENT_PATTERNS,
    SUPPORTED_EXPRESSION_CONSTRUCTORS,
)
from .protocol_values import (
    DeliveryEvent,
    ExternalEvent,
    FieldDeclaration,
    FieldStore,
    IRType,
    IRValue,
    Message,
    Node,
    ProtocolConfig,
    ProtocolIRValidationError,
    ProtocolState,
    RunOutcome,
    RunStatus,
    StartEvent,
    StepError,
    StepFailure,
    StepResult,
    StepSuccess,
    runtime_store,
    runtime_value,
    validate_field_store,
    validate_message_id,
)




__all__ = [
    "Action",
    "DeliveryEvent",
    "Expression",
    "FieldDeclaration",
    "IRType",
    "IRValue",
    "IRCapabilityManifest",
    "Message",
    "ProtocolConfig",
    "ProtocolIRValidationError",
    "ProtocolProgram",
    "ProtocolSignature",
    "ProtocolState",
    "Rule",
    "RuntimeContract",
    "RunOutcome",
    "RunStatus",
    "StartEvent",
    "StepError",
    "StepFailure",
    "StepSuccess",
    "SUPPORTED_ACTION_CONSTRUCTORS",
    "SUPPORTED_EVENT_PATTERNS",
    "SUPPORTED_EXPRESSION_CONSTRUCTORS",
    "decode_exported_config",
    "decode_exported_event",
    "decode_exported_state",
    "decode_ir_capability_manifest",
    "decode_protocol_program",
    "encode_exported_event",
    "encode_exported_run_outcome",
    "encode_exported_state",
    "encode_exported_step_result",
    "encode_exported_value",
    "evaluate_action",
    "evaluate_expression",
    "evaluate_state_predicate",
    "initialize_protocol",
    "interpret_step",
    "make_config",
    "make_delivery_event",
    "make_start_event",
    "run_schedule",
    "run_callback",
    "runtime_contract",
    "runtime_store",
    "runtime_value",
    "validate_field_store",
    "validate_message_id",
]
