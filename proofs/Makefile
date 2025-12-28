.PHONY: all clean extract melange setup

# This uses Rocq/Coq's makefile generator (ships with the prover distribution).
#
# Usage:
#   make        # build .vo files
#   make clean  # clean build artifacts
#
# It generates Makefile.coq locally, so the repo stays clean.

PROJECT_FILE := $(firstword $(wildcard _RocqProject) $(wildcard _CoqProject))

ifndef PROJECT_FILE
$(error No _RocqProject or _CoqProject found)
endif

MAKEFILE_GEN := $(shell command -v rocqmakefile 2>/dev/null || command -v rocq_makefile 2>/dev/null || command -v coq_makefile 2>/dev/null)

ifndef MAKEFILE_GEN
$(error No rocqmakefile/rocq_makefile/coq_makefile found in PATH)
endif

Makefile.coq: $(PROJECT_FILE)
	$(MAKEFILE_GEN) -f $(PROJECT_FILE) -o Makefile.coq

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall

# One-shot extraction without relying on Makefile.coq (useful for debugging).
# This will compile `theories/JanusProofs/FiniteDomain.v`, which contains an `Extraction ...`
# command at the bottom that writes `FiniteDomain.ml` (and usually `FiniteDomain.mli`)
# into the current working directory (i.e. `proofs/`).
COQC ?= coqc
extract:
	# Compile dependencies first (Coq loads `.vo` files for `Require`; it does not auto-compile `.v`).
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/FiniteDomain/Helpers.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/FiniteDomain/Model.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/FiniteDomain/Proofs.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/FiniteDomain.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/FiniteDomain/Extract.v

	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain/Intervals.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain/Domain.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain/UnionCanon.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain/Ops.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain/Proofs.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain.v
	$(COQC) -q -Q theories/JanusProofs JanusProofs theories/JanusProofs/ContiguousDomain/Extract.v

# Build JS output from extracted OCaml using Melange (requires dune + melange installed).
melange:
	dune build

# Local dev environment bootstrap (opam).
#
# NOTE: OCaml does not have an "8.18.0" release line; Coq does (Coq 8.18.0).
# If you *actually* meant to pin Coq to 8.18.0, keep COQ_VERSION=8.18.0 and pick
# an OCaml version compatible with that Coq release (default below).
#
# Override as needed:
#   make setup OPAM_SWITCH=janus-proofs OCAML_VERSION=4.14.1 COQ_VERSION=8.18.0
OPAM ?= opam
OPAM_SWITCH ?= janus-proofs
OCAML_VERSION ?= 4.14.1
COQ_VERSION ?= 8.18.0

setup:
	$(OPAM) init -y
	@if ! $(OPAM) switch list -s | grep -qx "$(OPAM_SWITCH)"; then \
		$(OPAM) switch create "$(OPAM_SWITCH)" "ocaml-base-compiler.$(OCAML_VERSION)" -y; \
	fi
	$(OPAM) install -y --switch "$(OPAM_SWITCH)" dune melange coq-lsp "coq.$(COQ_VERSION)"


