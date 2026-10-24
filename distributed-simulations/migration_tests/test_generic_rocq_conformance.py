import unittest

from distributed_simulations.algorithms import generated_echo_executable
from distributed_simulations.migration import generated_echo_program
from distributed_simulations.protocol_ir_codec import (
    decode_exported_config,
    decode_exported_event,
    decode_exported_state,
    decode_protocol_program,
    encode_exported_run_outcome,
    encode_exported_state,
    encode_exported_step_result,
)
from distributed_simulations.protocol_ir_interpreter import (
    initialize_protocol,
    interpret_step,
    run_schedule,
)


class GenericRocqConformanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = decode_protocol_program(
            generated_echo_program.PROTOCOL_TREE,
            node_decoder=int,
            expected_schema_version=generated_echo_program.SCHEMA_VERSION,
            expected_ir_version=generated_echo_program.IR_VERSION,
            expected_protocol_id=generated_echo_program.PROTOCOL_ID,
        )
        cls.export = generated_echo_program.ROCQ_CONFORMANCE_TREE

    def test_all_nine_rocq_computed_steps_match_python(self):
        raw_steps = self.export[1]
        self.assertEqual("steps", raw_steps[0])
        self.assertEqual(9, len(raw_steps) - 1)
        self.assertEqual(
            set(self.program.signature.rule_ids),
            {fixture[1] for fixture in raw_steps[1:]},
        )
        for fixture in raw_steps[1:]:
            _, name, raw_config, raw_state, raw_event, expected = fixture
            with self.subTest(rule=name):
                config = decode_exported_config(
                    self.program, raw_config, node_decoder=int
                )
                if name == "start":
                    state = initialize_protocol(self.program)
                    self.assertEqual(
                        raw_state, encode_exported_state(state, config.nodes)
                    )
                else:
                    state = decode_exported_state(
                        self.program, raw_state, node_decoder=int
                    )
                event = decode_exported_event(
                    self.program, raw_event, node_decoder=int
                )
                actual = interpret_step(
                    self.program, config, state, event
                )
                self.assertEqual(
                    expected, encode_exported_step_result(actual, config.nodes)
                )
                compiled = generated_echo_executable.step(config, state, event)
                self.assertEqual(actual, compiled)

    def test_rocq_computed_complete_run_matches_python(self):
        raw_runs = self.export[2]
        self.assertEqual("runs", raw_runs[0])
        _, name, raw_config, fuel, raw_events, expected = raw_runs[1]
        self.assertEqual("two-node-complete", name)
        config = decode_exported_config(
            self.program, raw_config, node_decoder=int
        )
        events = tuple(
            decode_exported_event(self.program, raw, node_decoder=int)
            for raw in raw_events[1:]
        )
        actual = run_schedule(self.program, config, int(fuel), events)
        self.assertEqual(
            expected, encode_exported_run_outcome(actual, config.nodes)
        )
        compiled = generated_echo_executable.run_schedule(
            config, int(fuel), events
        )
        self.assertEqual(actual, compiled)


if __name__ == "__main__":
    unittest.main()
