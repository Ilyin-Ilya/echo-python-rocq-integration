"""Compile a validated protocol IR program into readable Python source.

The compiler consumes the typed ``ProtocolProgram`` produced by the existing
decoder.  Its output calls only immutable runtime primitives; it does not ship
or interpret the serialized IR tree at runtime.
"""

from __future__ import annotations

import ast
import keyword
import re
from typing import Dict, List, Sequence

from distributed_simulations.protocol_compiled_runtime import (
    COMPILED_RUNTIME_ABI_VERSION,
    GENERATED_PROTOCOL_API_VERSION,
    GENERATED_PROTOCOL_PUBLIC_NAMES,
)
from distributed_simulations.protocol_ir_ast import (
    Action,
    Expression,
    IRCapabilityManifest,
    ProtocolProgram,
    Rule,
    SUPPORTED_ACTION_CONSTRUCTORS,
    SUPPORTED_EVENT_PATTERNS,
    SUPPORTED_EXPRESSION_CONSTRUCTORS,
)
from distributed_simulations.protocol_values import FieldStore, IRType, IRValue


class CompilationError(ValueError):
    """A validated IR construct has no Python code-generation rule."""


COMPILED_EXPRESSION_CONSTRUCTORS = (
    "literal",
    "config",
    "global",
    "local",
    "option-some",
    "option-get",
    "message-id",
    "message-sender",
    "message-receiver",
    "message-kind-is",
    "payload",
    "start-certificate",
    "delivery-certificate",
    "is-start",
    "is-delivery",
    "message-store-empty",
    "message-store-length",
    "next-message-id",
    "neighbors",
    "not",
    "and",
    "or",
    "equal",
    "option-is-some",
    "list-is-empty",
    "list-contains",
    "list-remove",
    "list-append",
    "list-permutation",
    "list-length",
    "nat-add",
    "nat-succ",
    "all-nodes-local-equal",
)
COMPILED_ACTION_CONSTRUCTORS = (
    "skip",
    "set-global",
    "set-local",
    "remove-selected-message",
    "emit",
    "emit-many",
    "sequence",
)
COMPILED_EVENT_PATTERNS = ("start", "deliver")


def validate_compiler_capabilities(
    manifest: IRCapabilityManifest | None = None,
) -> None:
    """Require the direct compiler to cover the complete declared IR surface."""

    required = (
        manifest.expressions
        if manifest is not None
        else SUPPORTED_EXPRESSION_CONSTRUCTORS,
        manifest.actions if manifest is not None else SUPPORTED_ACTION_CONSTRUCTORS,
        manifest.event_patterns
        if manifest is not None
        else SUPPORTED_EVENT_PATTERNS,
    )
    compiled = (
        COMPILED_EXPRESSION_CONSTRUCTORS,
        COMPILED_ACTION_CONSTRUCTORS,
        COMPILED_EVENT_PATTERNS,
    )
    labels = ("expressions", "actions", "event patterns")
    mismatches = []
    for label, expected, actual in zip(labels, required, compiled):
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        if missing or extra:
            mismatches.append(
                f"{label}: missing={missing!r}, extra={extra!r}"
            )
    if mismatches:
        raise CompilationError(
            "direct compiler capability mismatch: " + "; ".join(mismatches)
        )


def _identifier(value: str) -> str:
    rendered = re.sub(r"[^A-Za-z0-9_]", "_", value)
    if not rendered or rendered[0].isdigit() or keyword.iskeyword(rendered):
        rendered = "rule_" + rendered
    return rendered


def _type_source(kind: IRType) -> str:
    return f"IRType.{kind.name}"


def _value_source(value: IRValue) -> str:
    return f"IRValue({_type_source(value.kind)}, {value.value!r})"


def _store_source(store: FieldStore, indent: str = "") -> str:
    if not store:
        return "()"
    entries = "\n".join(
        f"{indent}    ({field!r}, {_value_source(value)}),"
        for field, value in store
    )
    return f"(\n{entries}\n{indent})"


def _string_tuple_source(values: Sequence[str], indent: str = "") -> str:
    if not values:
        return "()"
    entries = "\n".join(f"{indent}    {value!r}," for value in values)
    return f"(\n{entries}\n{indent})"


def _field_shape_source(fields: Sequence) -> str:
    if not fields:
        return "()"
    entries = "\n".join(
        f"    FieldDeclaration({field.name!r}, {_type_source(field.kind)}),"
        for field in fields
    )
    return f"(\n{entries}\n)"


class _Compiler:
    def __init__(self, program: ProtocolProgram):
        self.program = program
        self._message_name = None
        names = [_identifier(rule.identifier) for rule in program.rules]
        if len(set(names)) != len(names):
            raise CompilationError("rule identifiers collide as Python names")

    def expression(self, expression: Expression) -> str:
        op = expression.operator
        args = expression.arguments

        if op == "literal":
            return repr(args[0].value)
        if op == "config":
            return f"_config_{_identifier(args[0])}(config)"
        if op == "global":
            return f"_global_{_identifier(args[0])}(state)"
        if op == "local":
            return (
                f"_local_{_identifier(args[1])}(state, "
                f"{self.expression(args[0])})"
            )
        if op == "option-some":
            return self.expression(args[0])
        if op == "option-get":
            return f"runtime.option_get({self.expression(args[0])})"
        if op == "message-id":
            message = self._message_name or "runtime.message_for(event)"
            return f"{message}.identifier"
        if op == "message-sender":
            if self._message_name:
                return "sender"
            message = self._message_name or "runtime.message_for(event)"
            return f"{message}.sender"
        if op == "message-receiver":
            if self._message_name:
                return "receiver"
            message = self._message_name or "runtime.message_for(event)"
            return f"{message}.receiver"
        if op == "message-kind-is":
            message = self._message_name or "runtime.message_for(event)"
            return f"({message}.kind == {args[0]!r})"
        if op == "payload":
            message = self._message_name or "runtime.message_for(event)"
            return (
                f"runtime.lookup_value({message}.payload, "
                f"{args[0]!r})"
            )
        if op == "start-certificate":
            return (
                "runtime.lookup_value(runtime.start_certificates(event), "
                f"{args[0]!r})"
            )
        if op == "delivery-certificate":
            return (
                "runtime.lookup_value(runtime.delivery_certificates(event), "
                f"{args[0]!r})"
            )
        if op == "is-start":
            return "isinstance(event, runtime.ResolvedStart)"
        if op == "is-delivery":
            return "isinstance(event, runtime.ResolvedDelivery)"
        if op == "message-store-empty":
            return "(not state.messages)"
        if op == "message-store-length":
            return "len(state.messages)"
        if op == "next-message-id":
            return "state.next_message_id"
        if op == "neighbors":
            return f"config.neighbors_of({self.expression(args[0])})"
        if op == "not":
            operand = args[0]
            if operand.operator == "list-is-empty":
                return f"bool({self.expression(operand.arguments[0])})"
            if operand.operator == "equal":
                left, right = operand.arguments
                return f"({self.expression(left)} != {self.expression(right)})"
            return f"(not {self.expression(args[0])})"
        if op == "and":
            return (
                f"runtime.eager_and({self.expression(args[0])}, "
                f"{self.expression(args[1])})"
            )
        if op == "or":
            return (
                f"runtime.eager_or({self.expression(args[0])}, "
                f"{self.expression(args[1])})"
            )
        if op == "equal":
            left, right = args
            if right.operator == "literal" and right.arguments[0].value is None:
                return f"({self.expression(left)} is None)"
            if left.operator == "literal" and left.arguments[0].value is None:
                return f"({self.expression(right)} is None)"
            if right.operator == "literal" and right.arguments[0].value is True:
                return self.expression(left)
            if left.operator == "literal" and left.arguments[0].value is True:
                return self.expression(right)
            if right.operator == "literal" and right.arguments[0].value is False:
                return f"(not {self.expression(left)})"
            if left.operator == "literal" and left.arguments[0].value is False:
                return f"(not {self.expression(right)})"
            return f"({self.expression(left)} == {self.expression(right)})"
        if op == "option-is-some":
            return f"({self.expression(args[0])} is not None)"
        if op == "list-is-empty":
            return f"(not {self.expression(args[0])})"
        if op == "list-contains":
            return f"({self.expression(args[0])} in {self.expression(args[1])})"
        if op == "list-remove":
            return (
                f"runtime.remove_first({self.expression(args[0])}, "
                f"{self.expression(args[1])})"
            )
        if op == "list-append":
            return (
                f"(tuple({self.expression(args[0])}) + "
                f"tuple({self.expression(args[1])}))"
            )
        if op == "list-permutation":
            return (
                f"runtime.is_permutation({self.expression(args[0])}, "
                f"{self.expression(args[1])})"
            )
        if op == "list-length":
            return f"len({self.expression(args[0])})"
        if op == "nat-add":
            return f"({self.expression(args[0])} + {self.expression(args[1])})"
        if op == "nat-succ":
            return f"({self.expression(args[0])} + 1)"
        if op == "all-nodes-local-equal":
            return (
                f"runtime.all_nodes_local_equal(config, state, {args[0]!r}, "
                f"{self.expression(args[1])})"
            )
        raise CompilationError(f"unsupported expression constructor {op!r}")

    def expression_label(self, expression: Expression) -> str:
        """Derive a compact explanatory identifier from a typed expression."""

        op = expression.operator
        args = expression.arguments
        if op == "literal":
            value = args[0].value
            if value is None:
                return "none"
            if value == ():
                return "empty"
            return str(value).lower()
        if op in ("config", "global"):
            return _identifier(args[0])
        if op == "local":
            return _identifier(args[1])
        if op in ("message-id", "message-sender", "message-receiver"):
            return op.replace("message-", "")
        if op == "message-kind-is":
            return f"message_is_{_identifier(args[0])}"
        if op in ("payload", "start-certificate", "delivery-certificate"):
            return _identifier(args[0])
        if op == "is-start":
            return "event_is_start"
        if op == "is-delivery":
            return "event_is_delivery"
        if op == "message-store-empty":
            return "message_queue_is_empty"
        if op == "message-store-length":
            return "message_queue_length"
        if op == "next-message-id":
            return "next_message_id"
        if op == "neighbors":
            return f"{self.expression_label(args[0])}_neighbors"
        if op == "not":
            operand = args[0]
            if operand.operator == "equal":
                left, right = operand.arguments
                return (
                    f"{self.expression_label(left)}_is_not_"
                    f"{self.expression_label(right)}"
                )
            if operand.operator == "list-is-empty":
                return f"{self.expression_label(operand.arguments[0])}_is_not_empty"
            return f"not_{self.expression_label(operand)}"
        if op in ("and", "or"):
            return (
                f"{self.expression_label(args[0])}_{op}_"
                f"{self.expression_label(args[1])}"
            )
        if op == "equal":
            return (
                f"{self.expression_label(args[0])}_is_"
                f"{self.expression_label(args[1])}"
            )
        if op == "option-is-some":
            return f"{self.expression_label(args[0])}_is_set"
        if op == "option-get":
            return self.expression_label(args[0])
        if op == "list-is-empty":
            return f"{self.expression_label(args[0])}_is_empty"
        if op == "list-contains":
            return (
                f"{self.expression_label(args[1])}_contains_"
                f"{self.expression_label(args[0])}"
            )
        if op == "list-remove":
            if args[1].operator == "neighbors":
                return "forwarding_targets"
            return (
                f"{self.expression_label(args[1])}_without_"
                f"{self.expression_label(args[0])}"
            )
        if op == "list-append":
            return "appended_nodes"
        if op == "list-permutation":
            return "lists_are_permutations"
        if op == "list-length":
            return f"{self.expression_label(args[0])}_length"
        if op in ("nat-add", "nat-succ"):
            return "next_count"
        if op == "all-nodes-local-equal":
            return f"all_nodes_{_identifier(args[0])}_match"
        return op.replace("-", "_")

    @staticmethod
    def _unique_name(base: str, used: set[str]) -> str:
        base = _identifier(base)[:72]
        candidate = base
        suffix = 2
        while candidate in used:
            candidate = f"{base}_{suffix}"
            suffix += 1
        used.add(candidate)
        return candidate

    def _state_independent(self, expression: Expression) -> bool:
        """Whether an expression keeps its value across action state updates."""

        if expression.operator in {
            "global",
            "local",
            "message-store-empty",
            "message-store-length",
            "next-message-id",
            "all-nodes-local-equal",
        }:
            return False
        return all(
            self._state_independent(argument)
            for argument in expression.arguments
            if isinstance(argument, Expression)
        )

    def _action_expressions(self, action: Action) -> List[Expression]:
        op = action.operator
        args = action.arguments
        if op == "sequence":
            return self._action_expressions(args[0]) + self._action_expressions(
                args[1]
            )
        if op == "set-global":
            return [args[1]]
        if op == "set-local":
            return [args[0], args[2]]
        if op in ("emit", "emit-many"):
            return [args[1], args[2], *(value for _, value in args[3])]
        return []

    def action_bindings(self, action: Action) -> tuple[List[str], Dict[str, str]]:
        """Name repeated state-independent action expressions once."""

        expressions = self._action_expressions(action)
        counts: Dict[str, int] = {}
        candidates: Dict[str, Expression] = {}
        for expression in expressions:
            source = self.expression(expression)
            counts[source] = counts.get(source, 0) + 1
            candidates[source] = expression

        used = {"state", "event", "message", "sender", "receiver"}
        bindings: Dict[str, str] = {}
        lines = []
        repeated = [
            (source, candidates[source])
            for source, count in counts.items()
            if count > 1
            and self._state_independent(candidates[source])
            and source not in {"sender", "receiver", "True", "False", "None", "()"}
        ]
        for source, expression in sorted(repeated, key=lambda item: len(item[0])):
            name = self._unique_name(self.expression_label(expression), used)
            rendered = source
            for previous, previous_name in sorted(
                bindings.items(), key=lambda item: len(item[0]), reverse=True
            ):
                rendered = rendered.replace(previous, previous_name)
            bindings[source] = name
            lines.append(f"    {name} = {rendered}")
        return lines, bindings

    def action_expression(
        self, expression: Expression, bindings: Dict[str, str]
    ) -> str:
        source = self.expression(expression)
        for original, name in sorted(
            bindings.items(), key=lambda item: len(item[0]), reverse=True
        ):
            source = source.replace(original, name)
        return source

    def payload(self, payload: Sequence, bindings: Dict[str, str]) -> str:
        if not payload:
            return "()"
        fields = []
        for field, expression in payload:
            fields.append(
                f"({field!r}, IRValue({_type_source(expression.result_type)}, "
                f"{self.action_expression(expression, bindings)}))"
            )
        return "(" + ", ".join(fields) + ",)"

    def action_lines(
        self,
        action: Action,
        bindings: Dict[str, str],
        indent: str = "    ",
    ) -> List[str]:
        op = action.operator
        args = action.arguments
        if op == "skip":
            return []
        if op == "sequence":
            return self.action_lines(args[0], bindings, indent) + self.action_lines(
                args[1], bindings, indent
            )
        if op == "set-global":
            field, value = args
            field_name = _identifier(field)
            return [
                f"{indent}{field_name}_value = {self.action_expression(value, bindings)}",
                f"{indent}state = _set_global_{field_name}(",
                f"{indent}    state, {field_name}_value",
                f"{indent})",
            ]
        if op == "set-local":
            process, field, value = args
            field_name = _identifier(field)
            return [
                f"{indent}{field_name}_node = {self.action_expression(process, bindings)}",
                f"{indent}{field_name}_value = {self.action_expression(value, bindings)}",
                f"{indent}state = _set_local_{field_name}(",
                f"{indent}    state, {field_name}_node, {field_name}_value",
                f"{indent})",
            ]
        if op == "remove-selected-message":
            return [f"{indent}state = runtime.remove_selected_message(state, event)"]
        if op in ("emit", "emit-many"):
            kind, sender, receivers, payload = args
            helper = "emit_one" if op == "emit" else "emit_many"
            receiver_name = (
                "message_receiver" if op == "emit" else "message_receivers"
            )
            return [
                f"{indent}message_sender = {self.action_expression(sender, bindings)}",
                f"{indent}{receiver_name} = {self.action_expression(receivers, bindings)}",
                f"{indent}message_payload = {self.payload(payload, bindings)}",
                f"{indent}state = runtime.{helper}(",
                f"{indent}    state, {kind!r}, message_sender, {receiver_name},",
                f"{indent}    message_payload",
                f"{indent})",
            ]
        raise CompilationError(f"unsupported action constructor {op!r}")

    def rule_source(self, rule: Rule) -> str:
        name = _identifier(rule.identifier)
        pattern_kind = rule.pattern.kind
        message_kind = rule.pattern.message_kind
        self._message_name = "message" if pattern_kind == "deliver" else None
        lines = [
            f"def _check_{name}(config, state, event):",
            f"    # Generated guard for Rocq rule {rule.identifier!r}.",
            "    if not runtime.pattern_matches(",
            f"        event, {pattern_kind!r}, {message_kind!r}",
            "    ):",
            "        return runtime.RuleStatus.MISMATCH",
        ]
        if pattern_kind == "deliver":
            lines.extend(
                [
                    "    message = runtime.message_for(event)",
                    "    sender = message.sender",
                    "    receiver = message.receiver",
                ]
            )
        lines.append("    try:")
        used_guard_names = set()
        if not rule.guards:
            lines.append("        pass")
        for index, guard in enumerate(rule.guards, start=1):
            guard_source = self.expression(guard)
            guard_name = self._unique_name(
                f"guard_{self.expression_label(guard)}", used_guard_names
            )
            lines.extend(
                [
                    f"        # Formal guard {index}.",
                    f"        {guard_name} = {guard_source}",
                    f"        if not {guard_name}:",
                    "            return runtime.RuleStatus.DISABLED",
                ]
            )
        lines.extend(
            [
                "    except runtime.CompiledEvaluationFailure:",
                "        return runtime.RuleStatus.MALFORMED",
                "    return runtime.RuleStatus.ENABLED",
                "",
                "",
                f"def _apply_{name}(config, state, event):",
                f"    # Generated action for Rocq rule {rule.identifier!r}.",
            ]
        )
        if pattern_kind == "deliver":
            lines.extend(
                [
                    "    message = runtime.message_for(event)",
                    "    sender = message.sender",
                    "    receiver = message.receiver",
                ]
            )
        binding_lines, bindings = self.action_bindings(rule.action)
        lines.extend(binding_lines)
        action_lines = self.action_lines(rule.action, bindings)
        lines.extend(action_lines or ["    pass"])
        lines.append("    return state")
        self._message_name = None
        return "\n".join(lines)

    def predicate_source(self, name: str, expression: Expression) -> str:
        """Render a state predicate as named eager subconditions."""

        used = set()
        lines = [
            f"def {name}(config, state):",
            "    try:",
            "        event = runtime.QueryEvent()",
        ]

        def emit(candidate: Expression) -> str:
            if candidate.operator == "or":
                left = emit(candidate.arguments[0])
                right = emit(candidate.arguments[1])
                result = self._unique_name(self.expression_label(candidate), used)
                lines.extend(
                    [
                        f"        {result} = runtime.eager_or(",
                        f"            {left},",
                        f"            {right},",
                        "        )",
                    ]
                )
                return result

            result = self._unique_name(self.expression_label(candidate), used)
            lines.append(f"        {result} = {self.expression(candidate)}")
            return result

        def conjuncts(candidate: Expression) -> List[Expression]:
            if candidate.operator == "and":
                return conjuncts(candidate.arguments[0]) + conjuncts(
                    candidate.arguments[1]
                )
            return [candidate]

        conditions = [emit(condition) for condition in conjuncts(expression)]

        def eager_and_lines(names: Sequence[str], indent: str) -> List[str]:
            if len(names) == 1:
                return [f"{indent}{names[0]}"]
            return [
                f"{indent}runtime.eager_and(",
                f"{indent}    {names[0]},",
                *eager_and_lines(names[1:], indent + "    "),
                f"{indent})",
            ]

        lines.append("        return bool(")
        lines.extend(eager_and_lines(conditions, "            "))
        lines.append("        )")
        lines.extend(
            [
                "    except runtime.CompiledEvaluationFailure:",
                "        return None",
            ]
        )
        return "\n".join(lines)

    def step_source(self) -> str:
        lines = [
            "_RULES = (",
        ]
        for rule in self.program.rules:
            name = _identifier(rule.identifier)
            lines.append(
                f"    ({rule.identifier!r}, _check_{name}, _apply_{name}),"
            )
        lines.extend(
            [
                ")",
                "",
                "",
                "def step(config, state, external_event):",
                "    event = runtime.resolve_event(",
                "        state, external_event,",
                "        start_fields=START_CERTIFICATE_FIELDS,",
                "        delivery_fields=DELIVERY_CERTIFICATE_FIELDS,",
                "    )",
                "    if event is None:",
                "        return StepFailure(StepError.UNQUEUED_MESSAGE)",
                "    enabled = []",
                "    for rule_id, check, action in _RULES:",
                "        status = check(config, state, event)",
                "        if status is runtime.RuleStatus.MALFORMED:",
                "            return StepFailure(StepError.MALFORMED_GUARD)",
                "        if status is runtime.RuleStatus.ENABLED:",
                "            enabled.append((rule_id, action))",
            ]
        )
        lines.extend(
            [
                "    if not enabled:",
                "        return StepFailure(StepError.NO_ENABLED_RULE)",
                "    if len(enabled) != 1:",
                "        return StepFailure(StepError.AMBIGUOUS_ENABLED_RULES)",
                "    rule_id, action = enabled[0]",
                "    try:",
                "        successor = action(config, state, event)",
                "    except runtime.CompiledEvaluationFailure:",
                "        return StepFailure(StepError.MALFORMED_ACTION)",
                "    return StepSuccess(rule_id, successor)",
            ]
        )
        return "\n".join(lines)

    def field_helpers_source(self) -> str:
        """Generate typed, protocol-specific names around generic stores."""

        blocks = []
        for field in self.program.signature.config_fields:
            name = _identifier(field.name)
            blocks.append(
                "\n".join(
                    [
                        f"def _config_{name}(config):",
                        f"    return runtime.lookup_value(config.fields, {field.name!r})",
                    ]
                )
            )
        for field in self.program.signature.global_fields:
            name = _identifier(field.name)
            blocks.append(
                "\n".join(
                    [
                        f"def _global_{name}(state):",
                        f"    return runtime.lookup_value(state.globals, {field.name!r})",
                        "",
                        "",
                        f"def _set_global_{name}(state, value):",
                        "    return runtime.set_global(",
                        f"        state, {field.name!r}, {_type_source(field.kind)}, value",
                        "    )",
                    ]
                )
            )
        for field in self.program.signature.local_fields:
            name = _identifier(field.name)
            blocks.append(
                "\n".join(
                    [
                        f"def _local_{name}(state, node):",
                        f"    return runtime.local_value(state, node, {field.name!r})",
                        "",
                        "",
                        f"def _set_local_{name}(state, node, value):",
                        "    return runtime.set_local(",
                        f"        state, node, {field.name!r}, {_type_source(field.kind)}, value",
                        "    )",
                    ]
                )
            )
        return "\n\n\n".join(blocks)


def render_compiled_module(
    program: ProtocolProgram,
    *,
    rocq_program_digest: str,
    generated_by: str,
) -> str:
    """Render a standalone protocol-specific Python execution module."""

    validate_compiler_capabilities()
    compiler = _Compiler(program)
    header = f'''"""Direct protocol executable generated from the Rocq IR program.

Read ``_check_*`` functions as rule preconditions and ``_apply_*`` functions
as their state transitions.  ``step`` requires exactly one rule to be enabled.
Do not edit this file by hand; change the Rocq program or the generic compiler.
"""

# Generated by {generated_by}.
from distributed_simulations import protocol_compiled_runtime as runtime
from distributed_simulations.protocol_values import (
    FieldDeclaration,
    IRType,
    IRValue,
    ProtocolState,
    StepError,
    StepFailure,
    StepSuccess,
)


PROTOCOL_ID = {program.protocol_id!r}
SCHEMA_VERSION = {program.schema_version}
IR_VERSION = {program.ir_version}
ROCQ_PROGRAM_DIGEST = {rocq_program_digest!r}
RUNTIME_ABI_VERSION = {COMPILED_RUNTIME_ABI_VERSION}
runtime.require_runtime_abi(RUNTIME_ABI_VERSION)
GENERATED_API_VERSION = {GENERATED_PROTOCOL_API_VERSION}
LOCAL_FIELDS = {_field_shape_source(program.signature.local_fields)}
GLOBAL_FIELDS = {_field_shape_source(program.signature.global_fields)}
CONFIG_FIELDS = {_field_shape_source(program.signature.config_fields)}
PAYLOAD_FIELDS = {_field_shape_source(program.signature.payload_fields)}
START_CERTIFICATE_FIELDS = {_field_shape_source(program.signature.start_certificate_fields)}
DELIVERY_CERTIFICATE_FIELDS = {_field_shape_source(program.signature.delivery_certificate_fields)}
MESSAGE_KINDS = {_string_tuple_source(program.signature.message_kinds)}
RULE_IDS = {_string_tuple_source(program.signature.rule_ids)}


def make_config(*, nodes, neighbors, fields):
    return runtime.make_config(
        CONFIG_FIELDS,
        nodes=nodes,
        neighbors=neighbors,
        fields=fields,
    )


def make_start_event(fields):
    return runtime.make_start_event(START_CERTIFICATE_FIELDS, fields)


def make_delivery_event(message_id, fields):
    return runtime.make_delivery_event(
        DELIVERY_CERTIFICATE_FIELDS, message_id, fields
    )


def start_event(fields=None):
    return make_start_event({{}} if fields is None else fields)


def deliver(message_id, fields=None):
    return make_delivery_event(
        message_id, {{}} if fields is None else fields
    )


def initialize_protocol():
    return ProtocolState(
        default_local={_store_source(program.initial_local, "        ")},
        local_overrides=(),
        messages=(),
        globals={_store_source(program.initial_global, "        ")},
        next_message_id={program.initial_next_message_id},
    )
'''
    helpers = compiler.field_helpers_source()
    predicates = "\n\n\n".join(
        (
            compiler.predicate_source("is_complete", program.complete),
            compiler.predicate_source("is_stuck", program.stuck),
        )
    )
    rules = "\n\n\n".join(
        compiler.rule_source(rule) for rule in program.rules
    )
    step = compiler.step_source()
    footer = f'''


def run_schedule(config, fuel, schedule, state=None):
    return runtime.run_schedule(
        initialize=initialize_protocol,
        step=step,
        complete=is_complete,
        stuck=is_stuck,
        config=config,
        fuel=fuel,
        schedule=schedule,
        state=state,
    )


def run_callback(
    config,
    *,
    start_event,
    scheduler,
    delivery_event,
    max_steps=10_000,
    observer=None,
):
    return runtime.run_callback(
        initialize=initialize_protocol,
        step=step,
        complete=is_complete,
        stuck=is_stuck,
        config=config,
        start_event=start_event,
        scheduler=scheduler,
        delivery_event=delivery_event,
        max_steps=max_steps,
        observer=observer,
    )


__all__ = {GENERATED_PROTOCOL_PUBLIC_NAMES!r}
runtime.validate_generated_protocol_api(globals())
'''
    sections = [header, helpers, predicates, rules, step, footer]
    source = "\n\n\n".join(section for section in sections if section)
    ast.parse(source)
    return source


__all__ = [
    "COMPILED_ACTION_CONSTRUCTORS",
    "COMPILED_EVENT_PATTERNS",
    "COMPILED_EXPRESSION_CONSTRUCTORS",
    "CompilationError",
    "render_compiled_module",
    "validate_compiler_capabilities",
]
