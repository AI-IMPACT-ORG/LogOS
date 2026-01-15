# LogOS: an Agda research library for foundational logic system architecture.
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

AGDA        ?= agda
AGDA_FLAGS  ?= --no-libraries -i .
AGDA_WARN_FLAGS ?= -W all -W error
AGDA_CI_FLAGS ?= $(AGDA_FLAGS) $(AGDA_WARN_FLAGS)

.PHONY: help clean test tests docs ci ci-policy lint license-check license-headers-check honesty-check postulate-policy-check host-surface-check import-layer-check demo-isolation-check toy-sketch-location-check no-tabs-check doc-reference-check doc-module-check legacy-isolation-check surface-namespace-check kernel-antisymmetry-check vacuity-check correctness-check agda-lib-check packs packs-zfc packs-universality packs-opacity packs-complexity packs-agents check-all check-all-clean make-all check-all-agda check-all-docs html

help:
	@echo "Common targets:"
	@echo "  make ci         - policy checks + tests + docs"
	@echo "  make test       - type-check Tests/All.agda"
	@echo "  make vacuity-check - type-check vacuity-guard surfaces"
	@echo "  make correctness-check - type-check correctness surfaces"
	@echo "  make docs       - type-check curated docs entrypoints"
	@echo "  make packs      - type-check curated packs (heavier)"
	@echo "  make html       - build HTML docs into _build/html"
	@echo "  make check-all  - clean + full CI + type-check everything (release gate)"
	@echo "  make check-all-clean - alias for check-all"
	@echo "  make clean      - remove .agdai/.agda.err and _build/"

clean:
	@echo "Cleaning Agda artifacts..."
	@find . -type f -name '*.agdai' -delete 2>/dev/null || true
	@find . -type f -name '*.agda.err' -delete 2>/dev/null || true
	@rm -rf _build

test tests:
	$(AGDA) $(AGDA_CI_FLAGS) Tests/All.agda

# Fast path: tests only
.PHONY: fast
fast: tests

docs: doc-reference-check
	$(AGDA) $(AGDA_CI_FLAGS) docs/Library.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Definition.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Architecture_PortsAdapters.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Definition_Spec.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/Communication.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/AIAssistedModeling.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/CoreScience.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Views/HoTT_3Level.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Views/CategoricalLogic.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Views/MultiInstitution.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Views/ObserverSemantics.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Views/CurryHowardLambek.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Applications/ZFC.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/ZFC_Demo.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/Complexity.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Applications/Opacity.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Applications/Complexity.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Applications/Universality.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Applications/Agents.lagda.md

license-check:
	@bash scripts/check_gplv3_notice.sh

license-headers-check:
	@bash scripts/license_headers_check.sh

honesty-check:
	@bash scripts/honesty_check.sh

postulate-policy-check:
	@bash scripts/postulate_policy_check.sh

host-surface-check:
	@bash scripts/host_surface_check.sh

import-layer-check:
	@bash scripts/import_layer_check.sh

demo-isolation-check:
	@bash scripts/demo_isolation_check.sh

toy-sketch-location-check:
	@bash scripts/toy_sketch_location_check.sh

no-tabs-check:
	@bash scripts/no_tabs_check.sh

bad-code-smells-check:
	@bash scripts/bad_code_smells_check.sh

doc-reference-check:
	@bash scripts/doc_reference_check.sh

doc-module-check: doc-reference-check
	@bash scripts/doc_module_check.sh

legacy-isolation-check:
	@bash scripts/legacy_isolation_check.sh

surface-namespace-check:
	@bash scripts/surface_namespace_check.sh

agda-lib-check:
	@echo "Agda library-file smoke test (LogOS.agda-lib)..."
	@mkdir -p _build
	@printf '%s\n' "$(CURDIR)/LogOS.agda-lib" > _build/local.agda-libraries
	$(AGDA) --no-default-libraries --library-file=_build/local.agda-libraries -l LogOS $(AGDA_WARN_FLAGS) LogOS/API/Minimal.agda

ci-policy: license-check license-headers-check honesty-check postulate-policy-check host-surface-check import-layer-check demo-isolation-check toy-sketch-location-check no-tabs-check bad-code-smells-check doc-reference-check doc-module-check legacy-isolation-check surface-namespace-check kernel-antisymmetry-check

ci: ci-policy vacuity-check correctness-check tests docs

kernel-antisymmetry-check:
	@bash scripts/kernel_antisymmetry_check.sh

vacuity-check:
	$(AGDA) $(AGDA_CI_FLAGS) Tests/Vacuity.agda

correctness-check:
	$(AGDA) $(AGDA_CI_FLAGS) Tests/Correctness.agda

## Optional: type-check curated packs (heavier; not part of `ci` by default)
packs: packs-zfc packs-universality packs-opacity packs-complexity packs-agents

packs-zfc:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/ZFC/All.agda

packs-universality:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/Universality/All.agda

packs-opacity:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/Opacity/Experimental/All.agda

packs-complexity:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/Complexity/Experimental/All.agda

packs-agents:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/Agents/All.agda

lint:
	@echo "Lint: scanning for banned primitive imports (LogOS + Tests)..."
	@if command -v rg >/dev/null 2>&1; then \
		rg -n "^(open import|import) (Level|Data\\.Relation\\.Binary\\.PropositionalEquality|Agda\\.Builtin\\.Unit)([[:space:]]|$$)" \
			--glob 'LogOS/**' --glob 'Tests/**' \
			--glob '!Data/*' --glob '!**/*.lagda.md' \
			--glob '!LogOS/Prelude.agda' --glob '!LogOS/API/Minimal.agda' \
			--glob '!LogOS/Kernel/Hom.agda' --glob '!LogOS/Algebra/ConAlg.agda' --glob '!LogOS/Minimal/Con.agda' --glob '!LogOS/Minimal/Adapter.agda' ; \
		status="$$?" ; \
		if [ "$$status" -eq 2 ]; then \
			echo "Lint failed: rg regex error." ; exit 2 ; \
		elif [ "$$status" -eq 0 ]; then \
			echo "Found banned direct imports. Please use LogOS.Prelude." ; exit 1 ; \
		else \
			echo "Lint OK: no banned imports found." ; \
		fi ; \
	else \
		echo "Lint: rg not found; falling back to grep/find..." ; \
		out="$$(find LogOS Tests -type f -name '*.agda' -print0 2>/dev/null | xargs -0 grep -nE '^(open import|import) (Level|Data\\.Relation\\.Binary\\.PropositionalEquality|Agda\\.Builtin\\.Unit)([[:space:]]|$$)' 2>/dev/null || true)" ; \
		out="$$(printf '%s' "$$out" | grep -v -F 'LogOS/Prelude.agda:' || true)" ; \
		out="$$(printf '%s' "$$out" | grep -v -F 'LogOS/API/Minimal.agda:' || true)" ; \
		out="$$(printf '%s' "$$out" | grep -v -F 'LogOS/Kernel/Hom.agda:' || true)" ; \
		out="$$(printf '%s' "$$out" | grep -v -F 'LogOS/Algebra/ConAlg.agda:' || true)" ; \
		out="$$(printf '%s' "$$out" | grep -v -F 'LogOS/Minimal/Con.agda:' || true)" ; \
		out="$$(printf '%s' "$$out" | grep -v -F 'LogOS/Minimal/Adapter.agda:' || true)" ; \
		if [ -n "$$out" ]; then \
			echo "Found banned direct imports. Please use LogOS.Prelude." ; \
			echo "$$out" ; \
			exit 1 ; \
		else \
			echo "Lint OK: no banned imports found." ; \
		fi ; \
	fi

# Publication sanity: type-check every Agda source file in this repo.
#
# Note: this is intentionally heavier than `make ci` (which checks curated entrypoints).
check-all: clean ci-policy lint check-all-agda check-all-docs agda-lib-check

check-all-clean: check-all

# Readability alias: "make-all" = full publication sanity check.
make-all: check-all

check-all-agda:
	@echo "Type-checking all *.agda files..."
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_all_agda.sh

check-all-docs:
	@echo "Type-checking all *.lagda.md files..."
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_all_docs.sh

HTML_DIR ?= _build/html

html: doc-reference-check
	@echo "Building HTML docs into $(HTML_DIR)..."
	@mkdir -p "$(HTML_DIR)"
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Library.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Definition.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Architecture_PortsAdapters.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Definition_Spec.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/HoTT_3Level.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/CategoricalLogic.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/MultiInstitution.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/ObserverSemantics.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/CurryHowardLambek.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/ZFC.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/CoreScience.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/Communication.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/AIAssistedModeling.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/ZFC_Demo.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/Complexity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Opacity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Complexity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Universality.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Agents.lagda.md
	@bash scripts/write_html_index.sh "$(HTML_DIR)"
