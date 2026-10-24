COQBIN ?=
ROCQLIB ?=

# Use tools from PATH by default. COQBIN may name an installation-specific
# binary directory; normalize it so callers need not include a trailing slash.
ROCQ_BIN_DIR := $(if $(strip $(COQBIN)),$(patsubst %/,%,$(strip $(COQBIN)))/,)
# Rocq 9 installations may provide either the historical standalone
# `coq_makefile` alias or only the new `rocq makefile` command.
COQMAKEFILE := $(shell \
	if [ -x "$(ROCQ_BIN_DIR)coq_makefile" ]; then \
		printf '%s' '$(ROCQ_BIN_DIR)coq_makefile'; \
	elif [ -x "$(ROCQ_BIN_DIR)rocq" ]; then \
		printf '%s' '$(ROCQ_BIN_DIR)rocq makefile'; \
	elif command -v coq_makefile >/dev/null 2>&1; then \
		printf '%s' 'coq_makefile'; \
	elif command -v rocq >/dev/null 2>&1; then \
		printf '%s' 'rocq makefile'; \
	else \
		printf '%s' 'coq_makefile'; \
	fi)
ROCQ_ENV := $(if $(strip $(ROCQLIB)),ROCQLIB="$(ROCQLIB)",)

.PHONY: all migration clean

all: Makefile.coq
	$(ROCQ_ENV) $(MAKE) -f Makefile.coq COQBIN="$(ROCQ_BIN_DIR)"

Makefile.coq: _CoqProject
	$(ROCQ_ENV) $(COQMAKEFILE) -f _CoqProject -o Makefile.coq

migration: all Makefile.migration
	$(ROCQ_ENV) $(MAKE) -f Makefile.migration COQBIN="$(ROCQ_BIN_DIR)"

Makefile.migration: _CoqProject.migration
	$(ROCQ_ENV) $(COQMAKEFILE) -f _CoqProject.migration -o Makefile.migration

clean:
	@if [ -f Makefile.coq ]; then \
		$(ROCQ_ENV) $(MAKE) -f Makefile.coq COQBIN="$(ROCQ_BIN_DIR)" clean; \
	fi
	@if [ -f Makefile.migration ]; then \
		$(ROCQ_ENV) $(MAKE) -f Makefile.migration COQBIN="$(ROCQ_BIN_DIR)" clean; \
	fi
	$(RM) Makefile.coq Makefile.coq.conf \
		Makefile.migration Makefile.migration.conf
