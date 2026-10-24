"""Decode and encode the versioned protocol IR exchange format.

This module translates between Rocq-exported S-expressions and the typed AST
and runtime values.  It does not interpret expressions or execute actions.
"""

from __future__ import annotations

from typing import Any, Callable, Iterable, Optional, Sequence, Tuple

from .protocol_ir_ast import (
    Action,
    EventPattern,
    Expression,
    IRCapabilityManifest,
    ProtocolProgram,
    ProtocolSignature,
    Rule,
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
    StepFailure,
    StepSuccess,
)

SExpr = Any

def _expect_tuple(value: SExpr, head: Optional[str] = None, arity: Optional[int] = None) -> tuple:
    if not isinstance(value, tuple):
        raise ProtocolIRValidationError(f"expected S-expression list, got {value!r}")
    if head is not None and (not value or value[0] != head):
        raise ProtocolIRValidationError(f"expected ({head} ...), got {value!r}")
    if arity is not None and len(value) != arity:
        raise ProtocolIRValidationError(
            f"{head or 'S-expression'} expects {arity - 1} arguments, got {len(value) - 1}"
        )
    return value


def _expect_atom(value: SExpr, description: str) -> str:
    if not isinstance(value, str):
        raise ProtocolIRValidationError(f"{description} must be an atom, got {value!r}")
    return value


def _natural(atom: SExpr, description: str) -> int:
    text = _expect_atom(atom, description)
    if not text.isdecimal():
        raise ProtocolIRValidationError(f"{description} must be a natural number, got {text!r}")
    return int(text)


def _unique_atoms(values: Iterable[SExpr], description: str) -> Tuple[str, ...]:
    atoms = tuple(_expect_atom(value, description) for value in values)
    if len(set(atoms)) != len(atoms):
        raise ProtocolIRValidationError(f"duplicate {description}: {atoms!r}")
    return atoms


def decode_ir_capability_manifest(
    raw: SExpr,
    *,
    expected_schema_version: int = 1,
    expected_ir_version: int = 1,
) -> IRCapabilityManifest:
    """Validate Rocq's exhaustive constructor manifest against this runtime.

    Rocq classifies the actual typed expression and action syntax with
    exhaustive matches. This check makes a formal constructor addition or
    rename fail generation until the Python decoder/interpreter explicitly
    supports the same versioned capability set.
    """

    root = _expect_tuple(raw, "protocol-ir-capabilities", 7)
    schema = _expect_tuple(root[1], "schema-version", 2)
    ir = _expect_tuple(root[2], "ir-version", 2)
    schema_version = _natural(schema[1], "capability schema version")
    ir_version = _natural(ir[1], "capability IR version")
    sections = (
        (root[3], "types"),
        (root[4], "expressions"),
        (root[5], "actions"),
        (root[6], "event-patterns"),
    )
    decoded = tuple(
        _unique_atoms(
            _expect_tuple(section, head)[1:], f"capability {head[:-1]}"
        )
        for section, head in sections
    )
    manifest = IRCapabilityManifest(
        schema_version=schema_version,
        ir_version=ir_version,
        types=decoded[0],
        expressions=decoded[1],
        actions=decoded[2],
        event_patterns=decoded[3],
    )
    expected = IRCapabilityManifest(
        schema_version=expected_schema_version,
        ir_version=expected_ir_version,
        types=tuple(kind.value for kind in IRType),
        expressions=SUPPORTED_EXPRESSION_CONSTRUCTORS,
        actions=SUPPORTED_ACTION_CONSTRUCTORS,
        event_patterns=SUPPORTED_EVENT_PATTERNS,
    )
    if manifest != expected:
        raise ProtocolIRValidationError(
            "Rocq/Python IR capability mismatch: "
            f"expected {expected!r}, got {manifest!r}"
        )
    return manifest


def _field_declarations(section: SExpr, head: str) -> Tuple[FieldDeclaration, ...]:
    values = _expect_tuple(section, head)
    declarations = []
    for raw in values[1:]:
        field = _expect_tuple(raw, "field", 3)
        name = _expect_atom(field[1], f"{head} field name")
        try:
            kind = IRType(_expect_atom(field[2], f"type of {name}"))
        except ValueError as error:
            raise ProtocolIRValidationError(f"unknown IR type in {field!r}") from error
        declarations.append(FieldDeclaration(name, kind))
    if len({field.name for field in declarations}) != len(declarations):
        raise ProtocolIRValidationError(f"duplicate field declaration in {head}")
    return tuple(declarations)


def _field_kind(declarations: Sequence[FieldDeclaration], name: str, scope: str) -> IRType:
    for declaration in declarations:
        if declaration.name == name:
            return declaration.kind
    raise ProtocolIRValidationError(f"unknown {scope} field {name!r}")


def _decode_signature(raw: SExpr) -> ProtocolSignature:
    signature = _expect_tuple(raw, "signature", 9)
    local = _field_declarations(signature[1], "local-fields")
    global_fields = _field_declarations(signature[2], "global-fields")
    config = _field_declarations(signature[3], "config-fields")
    message_section = _expect_tuple(signature[4], "message-kinds")
    payload = _field_declarations(signature[5], "payload-fields")
    start = _field_declarations(signature[6], "start-certificate-fields")
    delivery = _field_declarations(signature[7], "delivery-certificate-fields")
    rule_section = _expect_tuple(signature[8], "rule-ids")
    return ProtocolSignature(
        local_fields=local,
        global_fields=global_fields,
        config_fields=config,
        message_kinds=_unique_atoms(message_section[1:], "message kind"),
        payload_fields=payload,
        start_certificate_fields=start,
        delivery_certificate_fields=delivery,
        rule_ids=_unique_atoms(rule_section[1:], "rule id"),
    )


def _decode_value(raw: SExpr, expected: IRType, node_decoder: Callable[[str], Node]) -> IRValue:
    value = _expect_tuple(raw)
    if not value or value[0] != expected.value:
        raise ProtocolIRValidationError(
            f"expected {expected.value} value, got {raw!r}"
        )
    try:
        if expected is IRType.BOOL:
            _expect_tuple(value, "bool", 2)
            atom = _expect_atom(value[1], "Boolean")
            if atom not in ("true", "false"):
                raise ProtocolIRValidationError(f"invalid Boolean atom {atom!r}")
            return IRValue(expected, atom == "true")
        if expected in (IRType.NAT, IRType.MESSAGE_REF):
            _expect_tuple(value, expected.value, 2)
            return IRValue(expected, _natural(value[1], expected.value))
        if expected is IRType.NODE:
            _expect_tuple(value, "node", 2)
            return IRValue(expected, node_decoder(_expect_atom(value[1], "node")))
        if expected is IRType.OPTION_NODE:
            _expect_tuple(value, "option-node", 2)
            if value[1] == "none":
                return IRValue(expected, None)
            some = _expect_tuple(value[1], "some", 2)
            return IRValue(expected, node_decoder(_expect_atom(some[1], "node")))
        if expected is IRType.LIST_NODE:
            return IRValue(
                expected,
                tuple(node_decoder(_expect_atom(item, "node")) for item in value[1:]),
            )
    except ProtocolIRValidationError:
        raise
    except (TypeError, ValueError) as error:
        raise ProtocolIRValidationError(f"invalid {expected.value} value {raw!r}") from error
    raise AssertionError(f"unhandled IR type {expected}")


def _decode_expr(
    raw: SExpr,
    signature: ProtocolSignature,
    node_decoder: Callable[[str], Node],
) -> Expression:
    if isinstance(raw, str):
        atomic = {
            "message-id": IRType.NAT,
            "message-sender": IRType.NODE,
            "message-receiver": IRType.NODE,
            "is-start": IRType.BOOL,
            "is-delivery": IRType.BOOL,
            "message-store-empty": IRType.BOOL,
            "message-store-length": IRType.NAT,
            "next-message-id": IRType.NAT,
        }
        if raw not in atomic:
            raise ProtocolIRValidationError(f"unknown expression atom {raw!r}")
        return Expression(raw, (), atomic[raw])

    expression = _expect_tuple(raw)
    if not expression:
        raise ProtocolIRValidationError("empty expression")
    operator = _expect_atom(expression[0], "expression constructor")

    if operator == "literal":
        _expect_tuple(expression, operator, 2)
        encoded = _expect_tuple(expression[1])
        if not encoded:
            raise ProtocolIRValidationError("empty literal value")
        try:
            kind = IRType(_expect_atom(encoded[0], "literal type"))
        except ValueError as error:
            raise ProtocolIRValidationError(f"unknown literal type {encoded!r}") from error
        return Expression(operator, (_decode_value(encoded, kind, node_decoder),), kind)

    field_reads = {
        "config": (signature.config_fields, "config"),
        "global": (signature.global_fields, "global"),
        "payload": (signature.payload_fields, "payload"),
        "start-certificate": (signature.start_certificate_fields, "start certificate"),
        "delivery-certificate": (
            signature.delivery_certificate_fields,
            "delivery certificate",
        ),
    }
    if operator in field_reads:
        _expect_tuple(expression, operator, 2)
        field = _expect_atom(expression[1], f"{operator} field")
        declarations, scope = field_reads[operator]
        return Expression(operator, (field,), _field_kind(declarations, field, scope))

    if operator == "local":
        _expect_tuple(expression, operator, 3)
        process = _decode_expr(expression[1], signature, node_decoder)
        _require_type(process, IRType.NODE, operator)
        field = _expect_atom(expression[2], "local field")
        return Expression(
            operator,
            (process, field),
            _field_kind(signature.local_fields, field, "local"),
        )

    if operator == "message-kind-is":
        _expect_tuple(expression, operator, 2)
        kind = _expect_atom(expression[1], "message kind")
        _require_member(kind, signature.message_kinds, "message kind")
        return Expression(operator, (kind,), IRType.BOOL)

    unary = {
        "option-some": (IRType.NODE, IRType.OPTION_NODE),
        "option-get": (IRType.OPTION_NODE, IRType.NODE),
        "neighbors": (IRType.NODE, IRType.LIST_NODE),
        "not": (IRType.BOOL, IRType.BOOL),
        "option-is-some": (IRType.OPTION_NODE, IRType.BOOL),
        "list-is-empty": (IRType.LIST_NODE, IRType.BOOL),
        "list-length": (IRType.LIST_NODE, IRType.NAT),
        "nat-succ": (IRType.NAT, IRType.NAT),
    }
    if operator in unary:
        _expect_tuple(expression, operator, 2)
        operand = _decode_expr(expression[1], signature, node_decoder)
        expected, result = unary[operator]
        _require_type(operand, expected, operator)
        return Expression(operator, (operand,), result)

    if operator == "equal":
        _expect_tuple(expression, operator, 3)
        left = _decode_expr(expression[1], signature, node_decoder)
        right = _decode_expr(expression[2], signature, node_decoder)
        if left.result_type is not right.result_type:
            raise ProtocolIRValidationError("equal operands have different IR types")
        return Expression(operator, (left, right), IRType.BOOL)

    binary = {
        "and": (IRType.BOOL, IRType.BOOL, IRType.BOOL),
        "or": (IRType.BOOL, IRType.BOOL, IRType.BOOL),
        "list-contains": (IRType.NODE, IRType.LIST_NODE, IRType.BOOL),
        "list-remove": (IRType.NODE, IRType.LIST_NODE, IRType.LIST_NODE),
        "list-append": (IRType.LIST_NODE, IRType.LIST_NODE, IRType.LIST_NODE),
        "list-permutation": (IRType.LIST_NODE, IRType.LIST_NODE, IRType.BOOL),
        "nat-add": (IRType.NAT, IRType.NAT, IRType.NAT),
    }
    if operator in binary:
        _expect_tuple(expression, operator, 3)
        left = _decode_expr(expression[1], signature, node_decoder)
        right = _decode_expr(expression[2], signature, node_decoder)
        left_type, right_type, result = binary[operator]
        _require_type(left, left_type, operator)
        _require_type(right, right_type, operator)
        return Expression(operator, (left, right), result)

    if operator == "all-nodes-local-equal":
        _expect_tuple(expression, operator, 3)
        field = _expect_atom(expression[1], "local field")
        expected_type = _field_kind(signature.local_fields, field, "local")
        expected = _decode_expr(expression[2], signature, node_decoder)
        _require_type(expected, expected_type, operator)
        return Expression(operator, (field, expected), IRType.BOOL)

    raise ProtocolIRValidationError(f"unknown expression constructor {operator!r}")


def _require_type(expression: Expression, expected: IRType, context: str) -> None:
    if expression.result_type is not expected:
        raise ProtocolIRValidationError(
            f"{context} requires {expected.value}, got {expression.result_type.value}"
        )


def _require_member(value: str, values: Sequence[str], description: str) -> None:
    if value not in values:
        raise ProtocolIRValidationError(f"unknown {description} {value!r}")


def _decode_payload_expressions(
    raw: SExpr,
    signature: ProtocolSignature,
    node_decoder: Callable[[str], Node],
) -> Tuple[Tuple[str, Expression], ...]:
    section = _expect_tuple(raw, "payload")
    decoded = []
    for item in section[1:]:
        field_entry = _expect_tuple(item, "field", 3)
        field = _expect_atom(field_entry[1], "payload field")
        kind = _field_kind(signature.payload_fields, field, "payload")
        expression = _decode_expr(field_entry[2], signature, node_decoder)
        _require_type(expression, kind, f"payload field {field}")
        decoded.append((field, expression))
    return tuple(decoded)


def _decode_action(
    raw: SExpr,
    signature: ProtocolSignature,
    node_decoder: Callable[[str], Node],
) -> Action:
    if isinstance(raw, str):
        if raw not in ("skip", "remove-selected-message"):
            raise ProtocolIRValidationError(f"unknown action atom {raw!r}")
        return Action(raw)
    action = _expect_tuple(raw)
    if not action:
        raise ProtocolIRValidationError("empty action")
    operator = _expect_atom(action[0], "action constructor")
    if operator == "set-global":
        _expect_tuple(action, operator, 3)
        field = _expect_atom(action[1], "global field")
        kind = _field_kind(signature.global_fields, field, "global")
        value = _decode_expr(action[2], signature, node_decoder)
        _require_type(value, kind, operator)
        return Action(operator, (field, value))
    if operator == "set-local":
        _expect_tuple(action, operator, 4)
        process = _decode_expr(action[1], signature, node_decoder)
        _require_type(process, IRType.NODE, operator)
        field = _expect_atom(action[2], "local field")
        kind = _field_kind(signature.local_fields, field, "local")
        value = _decode_expr(action[3], signature, node_decoder)
        _require_type(value, kind, operator)
        return Action(operator, (process, field, value))
    if operator in ("emit", "emit-many"):
        _expect_tuple(action, operator, 5)
        message_kind = _expect_atom(action[1], "message kind")
        _require_member(message_kind, signature.message_kinds, "message kind")
        sender = _decode_expr(action[2], signature, node_decoder)
        receivers = _decode_expr(action[3], signature, node_decoder)
        _require_type(sender, IRType.NODE, operator)
        _require_type(
            receivers,
            IRType.NODE if operator == "emit" else IRType.LIST_NODE,
            operator,
        )
        payload = _decode_payload_expressions(action[4], signature, node_decoder)
        return Action(operator, (message_kind, sender, receivers, payload))
    if operator == "sequence":
        _expect_tuple(action, operator, 3)
        return Action(
            operator,
            (
                _decode_action(action[1], signature, node_decoder),
                _decode_action(action[2], signature, node_decoder),
            ),
        )
    raise ProtocolIRValidationError(f"unknown action constructor {operator!r}")


def _decode_rule(
    raw: SExpr,
    signature: ProtocolSignature,
    node_decoder: Callable[[str], Node],
) -> Rule:
    rule = _expect_tuple(raw, "rule", 5)
    identifier = _expect_atom(rule[1], "rule id")
    _require_member(identifier, signature.rule_ids, "rule id")
    if rule[2] == "start":
        pattern = EventPattern("start")
    else:
        delivery = _expect_tuple(rule[2], "deliver", 2)
        message_kind = _expect_atom(delivery[1], "delivery message kind")
        _require_member(message_kind, signature.message_kinds, "message kind")
        pattern = EventPattern("deliver", message_kind)
    guards_section = _expect_tuple(rule[3], "guards")
    guards = tuple(
        _decode_expr(guard, signature, node_decoder) for guard in guards_section[1:]
    )
    for guard in guards:
        _require_type(guard, IRType.BOOL, "guard")
    return Rule(
        identifier,
        pattern,
        guards,
        _decode_action(rule[4], signature, node_decoder),
    )


def _decode_store(
    raw: SExpr,
    head: str,
    declarations: Sequence[FieldDeclaration],
    node_decoder: Callable[[str], Node],
) -> FieldStore:
    section = _expect_tuple(raw, head)
    if len(section) - 1 != len(declarations):
        raise ProtocolIRValidationError(f"{head} does not define every declared field")
    values = []
    for encoded, declaration in zip(section[1:], declarations):
        field = _expect_tuple(encoded, "field", 3)
        if field[1] != declaration.name:
            raise ProtocolIRValidationError(
                f"{head} must use canonical field order; expected {declaration.name!r}"
            )
        values.append(
            (declaration.name, _decode_value(field[2], declaration.kind, node_decoder))
        )
    return tuple(values)


def decode_protocol_program(
    envelope: SExpr,
    *,
    node_decoder: Callable[[str], Node] = lambda atom: atom,
    expected_schema_version: int = 1,
    expected_ir_version: int = 1,
    expected_protocol_id: Optional[str] = None,
) -> ProtocolProgram:
    """Validate and decode one canonical ``ProtocolIRExport`` envelope."""

    root = _expect_tuple(envelope, "protocol-ir", 6)
    schema_section = _expect_tuple(root[1], "schema-version", 2)
    ir_section = _expect_tuple(root[2], "ir-version", 2)
    id_section = _expect_tuple(root[3], "protocol-id", 2)
    schema_version = _natural(schema_section[1], "schema version")
    ir_version = _natural(ir_section[1], "IR version")
    protocol_id = _expect_atom(id_section[1], "protocol id")
    if schema_version != expected_schema_version:
        raise ProtocolIRValidationError(
            f"unsupported schema version {schema_version}; expected {expected_schema_version}"
        )
    if ir_version != expected_ir_version:
        raise ProtocolIRValidationError(
            f"unsupported IR version {ir_version}; expected {expected_ir_version}"
        )
    if expected_protocol_id is not None and protocol_id != expected_protocol_id:
        raise ProtocolIRValidationError(
            f"protocol id mismatch: expected {expected_protocol_id!r}, got {protocol_id!r}"
        )
    signature = _decode_signature(root[4])
    program = _expect_tuple(root[5], "program", 5)
    initial = _expect_tuple(program[1], "initial", 4)
    local = _decode_store(
        initial[1], "local-fields", signature.local_fields, node_decoder
    )
    globals_store = _decode_store(
        initial[2], "global-fields", signature.global_fields, node_decoder
    )
    next_id = _expect_tuple(initial[3], "next-message-id", 2)
    rules_section = _expect_tuple(program[2], "rules")
    rules = tuple(
        _decode_rule(rule, signature, node_decoder) for rule in rules_section[1:]
    )
    if len({rule.identifier for rule in rules}) != len(rules):
        raise ProtocolIRValidationError("program contains duplicate rule identifiers")
    complete_section = _expect_tuple(program[3], "complete", 2)
    stuck_section = _expect_tuple(program[4], "stuck", 2)
    complete = _decode_expr(complete_section[1], signature, node_decoder)
    stuck = _decode_expr(stuck_section[1], signature, node_decoder)
    _require_type(complete, IRType.BOOL, "complete predicate")
    _require_type(stuck, IRType.BOOL, "stuck predicate")
    return ProtocolProgram(
        protocol_id=protocol_id,
        schema_version=schema_version,
        ir_version=ir_version,
        signature=signature,
        initial_local=local,
        initial_global=globals_store,
        initial_next_message_id=_natural(next_id[1], "initial next message id"),
        rules=rules,
        complete=complete,
        stuck=stuck,
    )


def decode_exported_state(
    program: ProtocolProgram,
    raw: SExpr,
    *,
    node_decoder: Callable[[str], Node] = lambda atom: atom,
) -> ProtocolState:
    """Decode one canonical state emitted by ``ir_state_sexpr``.

    The finite process rows are represented as local overrides while the
    program's initial local store remains the value for every omitted node.
    This matches Rocq's total process map without making the Python runtime
    depend on a particular protocol or finite node type.
    """

    state = _expect_tuple(raw, "state", 5)
    process_section = _expect_tuple(state[1], "processes")
    processes = []
    for encoded in process_section[1:]:
        process = _expect_tuple(encoded, "process", 3)
        node = node_decoder(_expect_atom(process[1], "process node"))
        fields = _decode_store(
            process[2], "local-fields", program.signature.local_fields, node_decoder
        )
        processes.append((node, fields))
    if any(
        node == previous
        for index, (node, _fields) in enumerate(processes)
        for previous, _previous_fields in processes[:index]
    ):
        raise ProtocolIRValidationError("exported state contains duplicate processes")

    message_section = _expect_tuple(state[2], "messages")
    messages = []
    for encoded in message_section[1:]:
        message = _expect_tuple(encoded, "message", 6)
        kind = _expect_atom(message[2], "message kind")
        _require_member(kind, program.signature.message_kinds, "message kind")
        messages.append(
            Message(
                identifier=_natural(message[1], "message id"),
                kind=kind,
                sender=node_decoder(_expect_atom(message[3], "message sender")),
                receiver=node_decoder(_expect_atom(message[4], "message receiver")),
                payload=_decode_store(
                    message[5],
                    "payload",
                    program.signature.payload_fields,
                    node_decoder,
                ),
            )
        )

    next_id = _expect_tuple(state[4], "next-message-id", 2)
    return ProtocolState(
        default_local=program.initial_local,
        local_overrides=tuple(processes),
        messages=tuple(messages),
        globals=_decode_store(
            state[3],
            "global-fields",
            program.signature.global_fields,
            node_decoder,
        ),
        next_message_id=_natural(next_id[1], "next message id"),
    )


def decode_exported_config(
    program: ProtocolProgram,
    raw: SExpr,
    *,
    node_decoder: Callable[[str], Node] = lambda atom: atom,
) -> ProtocolConfig:
    """Decode one canonical configuration emitted by ``ir_config_sexpr``."""

    config = _expect_tuple(raw, "config", 4)
    node_section = _expect_tuple(config[1], "nodes")
    nodes = tuple(
        node_decoder(_expect_atom(encoded, "configured node"))
        for encoded in node_section[1:]
    )
    if any(
        node == previous
        for index, node in enumerate(nodes)
        for previous in nodes[:index]
    ):
        raise ProtocolIRValidationError("exported config contains duplicate nodes")

    topology = _expect_tuple(config[2], "topology")
    neighbors = []
    for encoded in topology[1:]:
        row = _expect_tuple(encoded, "neighbors")
        if len(row) < 2:
            raise ProtocolIRValidationError("neighbor row is missing its owner")
        owner = node_decoder(_expect_atom(row[1], "neighbor row owner"))
        adjacent = tuple(
            node_decoder(_expect_atom(candidate, "neighbor"))
            for candidate in row[2:]
        )
        neighbors.append((owner, adjacent))
    if tuple(owner for owner, _adjacent in neighbors) != nodes:
        raise ProtocolIRValidationError(
            "exported topology rows must follow the canonical node order"
        )

    return ProtocolConfig(
        nodes=nodes,
        neighbors=tuple(neighbors),
        fields=_decode_store(
            config[3],
            "config-fields",
            program.signature.config_fields,
            node_decoder,
        ),
    )


def decode_exported_event(
    program: ProtocolProgram,
    raw: SExpr,
    *,
    node_decoder: Callable[[str], Node] = lambda atom: atom,
) -> ExternalEvent:
    """Decode one external event emitted by ``ir_external_event_sexpr``."""

    event = _expect_tuple(raw)
    if event and event[0] == "start":
        _expect_tuple(event, "start", 2)
        return StartEvent(
            _decode_store(
                event[1],
                "certificates",
                program.signature.start_certificate_fields,
                node_decoder,
            )
        )
    if event and event[0] == "deliver":
        _expect_tuple(event, "deliver", 3)
        return DeliveryEvent(
            _natural(event[1], "delivered message id"),
            _decode_store(
                event[2],
                "certificates",
                program.signature.delivery_certificate_fields,
                node_decoder,
            ),
        )
    raise ProtocolIRValidationError(f"unknown exported event {raw!r}")


def encode_exported_value(
    value: IRValue,
    *,
    node_encoder: Callable[[Node], str] = str,
) -> tuple:
    """Encode a runtime value in the canonical Rocq export shape."""

    if value.kind is IRType.BOOL:
        return ("bool", "true" if value.value else "false")
    if value.kind in (IRType.NAT, IRType.MESSAGE_REF):
        return (value.kind.value, str(value.value))
    if value.kind is IRType.NODE:
        return ("node", node_encoder(value.value))
    if value.kind is IRType.OPTION_NODE:
        optional = (
            "none"
            if value.value is None
            else ("some", node_encoder(value.value))
        )
        return ("option-node", optional)
    if value.kind is IRType.LIST_NODE:
        return ("list-node", *(node_encoder(node) for node in value.value))
    raise ProtocolIRValidationError(f"unknown runtime value {value!r}")


def _encode_exported_store(
    head: str,
    fields: FieldStore,
    node_encoder: Callable[[Node], str],
) -> tuple:
    return (
        head,
        *(
            ("field", name, encode_exported_value(value, node_encoder=node_encoder))
            for name, value in fields
        ),
    )


def encode_exported_state(
    state: ProtocolState,
    nodes: Sequence[Node],
    *,
    node_encoder: Callable[[Node], str] = str,
) -> tuple:
    """Encode a Python state exactly as ``ir_state_sexpr`` does in Rocq."""

    processes = (
        "processes",
        *(
            (
                "process",
                node_encoder(node),
                _encode_exported_store(
                    "local-fields", state.local_fields(node), node_encoder
                ),
            )
            for node in nodes
        ),
    )
    messages = (
        "messages",
        *(
            (
                "message",
                str(message.identifier),
                message.kind,
                node_encoder(message.sender),
                node_encoder(message.receiver),
                _encode_exported_store("payload", message.payload, node_encoder),
            )
            for message in state.messages
        ),
    )
    return (
        "state",
        processes,
        messages,
        _encode_exported_store("global-fields", state.globals, node_encoder),
        ("next-message-id", str(state.next_message_id)),
    )


def encode_exported_event(
    event: ExternalEvent,
    *,
    node_encoder: Callable[[Node], str] = str,
) -> tuple:
    """Encode a Python external event in the canonical Rocq export shape."""

    if isinstance(event, StartEvent):
        certificates = _encode_exported_store(
            "certificates", event.certificates, node_encoder
        )
        return ("start", certificates)
    if isinstance(event, DeliveryEvent):
        certificates = _encode_exported_store(
            "certificates", event.certificates, node_encoder
        )
        return ("deliver", str(event.message_id), certificates)
    raise ProtocolIRValidationError(f"unknown external event {event!r}")


def encode_exported_step_result(
    result: StepResult,
    nodes: Sequence[Node],
    *,
    node_encoder: Callable[[Node], str] = str,
) -> tuple:
    """Encode a Python step result for direct comparison with Rocq."""

    if isinstance(result, StepSuccess):
        return (
            "success",
            result.rule_id,
            encode_exported_state(result.state, nodes, node_encoder=node_encoder),
        )
    if isinstance(result, StepFailure):
        return ("failure", result.error.value)
    raise ProtocolIRValidationError(f"unknown step result {result!r}")


def encode_exported_run_outcome(
    outcome: RunOutcome,
    nodes: Sequence[Node],
    *,
    node_encoder: Callable[[Node], str] = str,
) -> tuple:
    """Encode a Python run outcome for direct comparison with Rocq."""

    encoded_state = encode_exported_state(
        outcome.state, nodes, node_encoder=node_encoder
    )
    if outcome.status is not RunStatus.INVALID:
        return (outcome.status.value, str(outcome.steps), encoded_state)
    optional_event: Any = (
        "none"
        if outcome.event is None
        else (
            "some",
            encode_exported_event(outcome.event, node_encoder=node_encoder),
        )
    )
    return (
        "invalid",
        str(outcome.steps),
        optional_event,
        outcome.error,
        encoded_state,
    )


__all__ = [
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
]
