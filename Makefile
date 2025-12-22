# LogOS: an Agda Library for foundational logic architecture
# Copyright (C) 2025 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

AGDA        ?= agda
AGDA_FLAGS  ?= --no-libraries -i .
AGDA_WARN_FLAGS ?= -W all -W error

.PHONY: help clean test tests docs ci lint license-check license-headers-check honesty-check postulate-policy-check host-surface-check import-layer-check demo-isolation-check toy-sketch-location-check no-tabs-check doc-reference-check packs packs-zfc packs-universality check-all make-all check-all-agda check-all-docs html

help:
	@echo "Common targets:"
	@echo "  make ci         - policy checks + tests + docs"
	@echo "  make test       - type-check Tests/All.agda"
	@echo "  make docs       - type-check curated docs entrypoints"
	@echo "  make packs      - type-check curated packs (heavier)"
	@echo "  make html       - build HTML docs into _build/html"
	@echo "  make check-all  - type-check everything with -W error (heaviest)"
	@echo "  make clean      - remove .agdai/.agda.err and _build/"

clean:
	@echo "Cleaning Agda artifacts..."
	@find . -type f -name '*.agdai' -delete 2>/dev/null || true
	@find . -type f -name '*.agda.err' -delete 2>/dev/null || true
	@rm -rf _build

test tests:
	$(AGDA) $(AGDA_FLAGS) Tests/All.agda

# Fast path: tests only
.PHONY: fast
fast: tests

docs: doc-reference-check
	$(AGDA) $(AGDA_FLAGS) docs/Library.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Packs.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Definition.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Definition_Spec.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/View_HoTT_3Level.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/View_CategoricalLogic.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/View_MultiInstitution.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/View_ObserverSemantics.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Application_ZFC.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/ZFC_Demo.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Complexity.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Application_Opacity.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Application_PvsNP.lagda.md
	$(AGDA) $(AGDA_FLAGS) docs/Application_Universality.lagda.md

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

doc-reference-check:
	@bash scripts/doc_reference_check.sh

ci: license-check license-headers-check honesty-check postulate-policy-check host-surface-check import-layer-check demo-isolation-check toy-sketch-location-check no-tabs-check doc-reference-check tests docs

## Optional: type-check curated packs (heavier; not part of `ci` by default)
packs: packs-zfc packs-universality

packs-zfc:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/ZFC/All.agda

packs-universality:
	$(AGDA) $(AGDA_FLAGS) LogOS/Packs/Universality/All.agda

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
# Note: this is intentionally heavier than `make ci` (which checks the curated entrypoints).
check-all: check-all-agda check-all-docs

# Readability alias: "make-all" = full publication sanity check.
make-all: check-all

check-all-agda:
	@echo "Type-checking all *.agda files..."
	@find . -type f -name '*.agda' -not -path './_build/*' -print0 \
		| xargs -0 -n 1 $(AGDA) $(AGDA_FLAGS) $(AGDA_WARN_FLAGS)

check-all-docs:
	@echo "Type-checking all *.lagda.md files..."
	@find . -type f -name '*.lagda.md' -not -path './_build/*' -print0 \
		| xargs -0 -n 1 $(AGDA) $(AGDA_FLAGS) $(AGDA_WARN_FLAGS)

HTML_DIR ?= _build/html

html: doc-reference-check
	@echo "Building HTML docs into $(HTML_DIR)..."
	@mkdir -p "$(HTML_DIR)"
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Library.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Packs.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Definition.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Definition_Spec.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/View_HoTT_3Level.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/View_CategoricalLogic.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/View_MultiInstitution.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/View_ObserverSemantics.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Application_ZFC.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/ZFC_Demo.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Complexity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Application_Opacity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Application_PvsNP.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Application_Universality.lagda.md
	@bash scripts/write_html_index.sh "$(HTML_DIR)"
