# Human adapter boundary

The project automates the protocol computation frame. It does not attempt to
generate an entire Python application or invent protocol-specific integration
policy.

## Generated and interpreter-owned

- typed state, message, expression, and action representations;
- initial state;
- transition rules and unique rule selection;
- successor-state construction;
- completion and stuck predicates;
- schema/version validation;
- data-only Python program generation;
- generic execution, replay, and freshness tests.

The scheduler cannot select a rule or provide a successor state.

## Human-authored in Rocq

- the protocol signature and IR program;
- protocol-specific invariants and proofs worth claiming;
- any new generic IR operation that is justified by more than one protocol.

## Human-authored in Python

- conversion from application topology/configuration into typed IR config;
- scheduling policy;
- input parsing, logging, tracing, UI, networking, and result presentation.

These Python functions may inspect formal state, but they do not implement a
second transition function.

## Inspecting the required hooks

After decoding a generated program, use `runtime_contract(program)`:

```python
contract = runtime_contract(program)
print(contract.config_fields)
print(contract.message_kinds)
print(contract.payload_fields)
```

Rule identifiers are available as `diagnostic_rule_ids` for errors and traces.
They are not an argument to `run_callback`.

Each human adapter should validate the contract it expects. Echo does this in
`validate_echo_adapter_contract`: if a Rocq field or message shape changes,
the application fails at load time with a request to update the adapter instead
of silently executing with a stale interpretation. Echo also asserts that both
generic event-input field sets are empty.

## Minimal execution shape

```python
result = run_callback(
    program,
    human_config,
    start_event=echo_start_event(program),
    scheduler=choose_queued_message_id,
    delivery_event=lambda message_id: echo_delivery_event(
        program, message_id=message_id
    ),
    observer=record_or_display_state,
)
```

This is the intended reusable architecture: generated formal computation in
the middle, with small and understandable human adapters at the boundaries.
