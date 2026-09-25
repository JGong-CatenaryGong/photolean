# PhotoLean convenience targets (no dependencies beyond python3 and the repository scripts).

SHELL := /bin/bash
THEORIES := Marcus Hammond BEP Kasha Sabatier Goldschmidt SymmetryFactor KashaVavilov SternVolmer \
            QuantumYield FluorPhos EnergyGapLaw StokesShift ICvsISC Forster Einstein RACI

.PHONY: help build gate probes axioms counts figures check all clean-scratch

help:
	@echo "make build     - build every defaultTarget (needs the Lean toolchain)"
	@echo "make gate      - whole-tree gate: build + strict scan + leaf data planes"
	@echo "make probes    - the 17 statement-fidelity probes"
	@echo "make counts    - census: every number quoted by the manuscript, quoted vs computed"
	@echo "make figures   - regenerate paper/figures/fig1..3 (pdf + png)"
	@echo "make axioms    - exhaustive #print axioms sweep (minutes, needs Lean)"
	@echo "make check     - fast dependency-light checks (no Lean): CI parity"
	@echo "make all       - gate + probes + counts + figures"

build:
	proofs/scripts/lake build

gate:
	proofs/scripts/check.sh --strict

probes:
	@for T in $(THEORIES); do python3 theories/BEP/probes/bep-fidelity.py --theory $$T; done

counts:
	python3 tools/counts.py --md

figures:
	python3 paper/figures/make_figures.py

axioms:
	python3 tools/counts.py --axioms

check:
	python3 .github/scripts/strict_scan.py
	python3 .github/scripts/default_targets.py
	@for T in $(THEORIES); do \
	  python3 theories/BEP/probes/bep-fidelity.py --theory $$T | grep -q 'signature differences *: 0' \
	    || { echo "probe FAILED: $$T"; exit 1; }; \
	done
	@echo "fast checks OK"

all: gate probes counts figures

clean-scratch:
	rm -rf .lake/tmp/repro .lake/tmp/audit .lake/tmp/fresh-clone
