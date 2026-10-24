"""Optional replay of vectors from the retired Echo-specific Rocq model."""

import unittest
from dataclasses import replace

from distributed_simulations.migration import generated_echo_oracles
from distributed_simulations.migration.echo_ir_adapter import (
    EchoMessageView,
    EchoProcessView,
    decode_echo_state,
    echo_config,
    echo_delivery_event,
    echo_start_event,
    encode_echo_state,
    load_echo_program,
    validate_echo_adapter_contract,
)
from distributed_simulations.protocol_ir_interpreter import (
    interpret_step,
    run_schedule,
)
from distributed_simulations.protocol_values import (
    ProtocolIRValidationError,
    RunStatus,
    StepFailure,
    StepSuccess,
)


RULE_TO_VECTOR = {
    "start": "start",
    "first-request-nonleaf": "first-echo-nonleaf",
    "first-request-leaf": "first-echo-leaf",
    "repeated-request": "repeated-echo",
    "initiator-request": "initiator-echo",
    "participant-reply-more": "participant-ack-more",
    "participant-reply-final": "participant-ack-final",
    "initiator-reply-more": "initiator-ack-more",
    "initiator-reply-final": "initiator-ack-final",
}


def _parent(value):
    return None if value == "none" else int(value[1])


def _message(value):
    if value == "no-message":
        return None
    return EchoMessageView(
        int(value[1]), value[2].upper(), int(value[3]), int(value[4])
    )


def _state(value):
    return {
        "processes": {
            int(process[1]): EchoProcessView(
                _parent(process[2]),
                tuple(int(node) for node in process[3][1:]),
                process[4] == "true",
            )
            for process in value[3][1:]
        },
        "messages": tuple(_message(message) for message in value[4][1:]),
        "started": value[1] == "true",
        "next_message_id": int(value[2]),
    }


def _config(program, value):
    nodes = tuple(int(node) for node in value[2][1:])
    adjacency = {
        int(row[1]): tuple(int(node) for node in row[2:])
        for row in value[3][1:]
    }
    initiator = int(value[1])
    return (
        echo_config(
            program,
            initiator=initiator,
            nodes=nodes,
            adjacency=adjacency,
        ),
        nodes,
    )


def _event(program, value):
    message = _message(value[2])
    if message is None:
        return echo_start_event(program)
    return echo_delivery_event(
        program,
        message_id=message.message_id,
    )


def _encode(program, value):
    return encode_echo_state(program, **_state(value))


def _expected_view(value):
    state = _state(value)
    return (
        tuple(state["processes"].items()),
        state["messages"],
        state["started"],
        state["next_message_id"],
    )


def _actual_view(state, nodes):
    decoded = decode_echo_state(state, nodes)
    return (
        decoded.processes,
        decoded.messages,
        decoded.started,
        decoded.next_message_id,
    )


class GenericEchoIRVectorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = load_echo_program()

    def test_all_rocq_single_step_vectors(self):
        exported = generated_echo_oracles.ROCQ_EVALUATION_VECTORS
        config, nodes = _config(self.program, exported[1])
        for vector in exported[2:]:
            name = vector[1]
            with self.subTest(vector=name):
                state = _encode(self.program, vector[2])
                event = _event(self.program, vector[3])
                result = interpret_step(self.program, config, state, event)
                expected = vector[4]
                if name == "invalid-first-echo-nonleaf-order":
                    # This vector was invalid only because its retired ordering
                    # certificate was wrong. Delivery events no longer carry
                    # certificates, so the queued message is now valid.
                    self.assertIsInstance(result, StepSuccess)
                    self.assertEqual("first-request-nonleaf", result.rule_id)
                    continue
                if expected == "none":
                    self.assertIsInstance(result, StepFailure)
                    continue
                self.assertIsInstance(result, StepSuccess)
                self.assertEqual(name, RULE_TO_VECTOR[result.rule_id])
                self.assertEqual(
                    _expected_view(expected[1]),
                    _actual_view(result.state, nodes),
                )

    def test_adapter_contract_rejects_formal_signature_drift(self):
        config_fields = self.program.signature.config_fields
        renamed = replace(config_fields[0], name="renamed-initiator")
        changed_signature = replace(
            self.program.signature,
            config_fields=(renamed,) + config_fields[1:],
        )
        changed_program = replace(self.program, signature=changed_signature)

        with self.assertRaisesRegex(
            ProtocolIRValidationError,
            "update echo_ir_adapter.py",
        ):
            validate_echo_adapter_contract(changed_program)

    def test_all_rocq_complete_run_vectors(self):
        status_map = {
            "complete": RunStatus.COMPLETE,
            "stuck": RunStatus.STUCK,
            "bounded": RunStatus.BOUNDED,
            "invalid-choice": RunStatus.INVALID,
        }
        for vector in generated_echo_oracles.ROCQ_RUN_VECTORS[1:]:
            name = vector[1]
            with self.subTest(vector=name):
                config, nodes = _config(self.program, vector[2])
                initial = _encode(self.program, vector[4])
                schedule = tuple(
                    _event(self.program, event)
                    for event in vector[5][1:]
                )
                outcome = run_schedule(
                    self.program,
                    config,
                    int(vector[3]),
                    schedule,
                    state=initial,
                )
                expected = vector[6]
                if name == "invalid-start":
                    # The old vector was invalid only because startup supplied
                    # a bad ordering certificate. Certificate-free startup is
                    # valid and exhausts this vector's zero remaining fuel.
                    self.assertIs(RunStatus.BOUNDED, outcome.status)
                    continue
                self.assertIs(status_map[expected[0]], outcome.status)
                self.assertEqual(int(expected[1]), outcome.steps)
                self.assertEqual(
                    _expected_view(expected[2]),
                    _actual_view(outcome.state, nodes),
                )


if __name__ == "__main__":
    unittest.main()
