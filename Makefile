.PHONY: help verify quick proof regenerate generated migration-proof \
	migration-generated regenerate-migration compare test-python evaluate

ROCQ_ARGS = $(if $(strip $(COQBIN)),COQBIN="$(COQBIN)") \
	$(if $(strip $(ROCQLIB)),ROCQLIB="$(ROCQLIB)")

help:
	@printf '%s\n' \
	  'make verify       build maintained proofs and run the integration gate' \
	  'make quick        check generated files and run Python tests' \
	  'make proof        build the maintained Rocq development' \
	  'make regenerate   build Rocq and regenerate the Python executable' \
	  'make generated    check that generated Python matches compiled Rocq' \
	  'make compare      build/check optional legacy oracles and compare them' \
	  'make regenerate-migration  regenerate optional serialized and oracle data' \
	  'make test-python  run Python unit and integration tests' \
	  'make evaluate     run bounded schedule and mutation evaluation'

verify:
	$(ROCQ_ARGS) ./verify_echo_integration.sh

quick: generated test-python

proof:
	$(MAKE) -C echo-algorithm-coq $(ROCQ_ARGS)

regenerate: proof
	cd distributed-simulations && python3 tools/generate_echo_program_from_rocq.py

generated:
	cd distributed-simulations && python3 tools/generate_echo_program_from_rocq.py --check

migration-proof:
	$(MAKE) -C echo-algorithm-coq migration $(ROCQ_ARGS)

migration-generated: migration-proof
	cd distributed-simulations && python3 tools/generate_echo_migration_data_from_rocq.py --check
	cd distributed-simulations && python3 tools/generate_echo_oracles_from_rocq.py --check

regenerate-migration: migration-proof
	cd distributed-simulations && python3 tools/generate_echo_migration_data_from_rocq.py
	cd distributed-simulations && python3 tools/generate_echo_oracles_from_rocq.py

compare: migration-generated
	cd distributed-simulations && python3 -m unittest discover -s migration_tests -v

test-python:
	cd distributed-simulations && python3 -m unittest discover -s tests -v

evaluate:
	cd distributed-simulations && python3 -m distributed_simulations.algorithms.echo_evaluation
