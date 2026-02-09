# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

AGDA        ?= agda

# Default mode is strict: exact splitting + full warnings.
#
# Rationale: `--no-exact-split` weakens coverage checking and can hide
# refactor-induced issues. Keep a separate opt-in "fast" mode for workflows
# that need legacy splitting.
AGDA_FLAGS_BASE   ?= --no-libraries -i . --safe
AGDA_FLAGS_STRICT ?= $(AGDA_FLAGS_BASE)
AGDA_FLAGS_FAST   ?= $(AGDA_FLAGS_BASE) --no-exact-split

AGDA_WARN_FLAGS_STRICT ?= -W all -W error
AGDA_WARN_FLAGS_FAST   ?= -W all -W noCoverageNoExactSplit -W error

AGDA_FLAGS       ?= $(AGDA_FLAGS_STRICT)
AGDA_WARN_FLAGS  ?= $(AGDA_WARN_FLAGS_STRICT)
PIPELINE_PROFILE ?= 0
PIPELINE_SKIP    ?= 0
AGDA_CI_FLAGS ?= $(AGDA_FLAGS) $(AGDA_WARN_FLAGS)

.PHONY: help clean test tests examples docs docs-curated ci ci-policy lint shellcheck license-check license-headers-check sync-license-headers ci-workflow-policy-check honesty-check postulate-policy-check safe-options-check host-surface-check host-import-check minimal-api-no-axioms-check api-no-axioms-check pack-trust-check readme-pack-trust-check agda-lib-policy-check import-layer-check layer-order-check operational-no-theorems-imports-check topic-kernel-api-check topic-all-index-check demo-isolation-check sketch-location-check no-tabs-check dangerous-pragmas-check stable-surface-no-experimental-imports-check stable-surface-no-guardless-exports-check stable-surface-no-internal-mu-imports-check stable-surface-no-kernel-io-imports-check stable-surface-no-domain-imports-check stable-surface-no-meta-assumption-imports-check stable-surface-no-banned-transitive-imports-check stable-surface-lock-check mk-satsystem-policy-check relation-symbol-governance-check doc-style-lint-check claim-stamp-check doc-analogy-markers-check doc-internal-imports-check bad-code-smells-check doc-reference-check doc-module-check surface-namespace-check kernel-antisymmetry-check assumption-boundary-check assumptions-ledger-check reachability-check vacuity-check correctness-check agda-lib-check packs packs-strict packs-zfc packs-universality packs-opacity packs-complexity packs-agents check-quick check-quick-no-transformer check-all check-all-clean check-all-warm make-all check-all-agda check-all-docs html depgraph

help:
	@echo "Common targets:"
	@echo "  make ci         - policy checks + tests + docs"
	@echo "  make test       - type-check Tests/All.agda"
	@echo "  make examples   - type-check Examples/*.agda"
	@echo "  make fast       - tests with legacy splitting (no-exact-split)"
	@echo "  make shellcheck - run shellcheck over scripts/*.sh + scripts/lib/*.sh"
	@echo "  make claim-stamp-check - validate claim-stamp sidecar syntax/coverage"
	@echo "  make sync-license-headers - rewrite legacy header title lines to canonical title"
	@echo "  make vacuity-check - type-check vacuity-guard surfaces"
	@echo "  make correctness-check - type-check correctness surfaces"
	@echo "  make docs       - type-check all docs (*.lagda.md)"
	@echo "  make docs-curated - type-check curated docs entrypoints"
	@echo "  make packs      - type-check curated packs (heavier)"
	@echo "  make packs-strict - same as packs (strict warnings)"
	@echo "  make html       - build HTML docs into _build/html"
	@echo "  make depgraph   - generate import dependency graphs into _build/depgraph"
	@echo "  make check-quick - warm dev check (policy + all *.agda + agda-lib smoke)"
	@echo "  make check-quick-no-transformer - warm dev check excluding transformer pipeline"
	@echo "  make check-all  - cold full check (clean + policy + all *.agda/*.lagda.md + agda-lib)"
	@echo "  make clean      - remove .agdai/.agda.err and _build/"

clean:
	@echo "Cleaning Agda artifacts..."
	@find . -type f -name '*.agdai' -delete 2>/dev/null || true
	@find . -type f -name '*.agda.err' -delete 2>/dev/null || true
	@rm -rf _build
	@find . -type d -name '__pycache__' -prune -exec rm -rf {} + 2>/dev/null || true
	@find . -type f -name '*.pyc' -delete 2>/dev/null || true

test tests:
	$(AGDA) $(AGDA_CI_FLAGS) Tests/All.agda

examples:
	$(AGDA) $(AGDA_CI_FLAGS) Examples/HelloMinimal.agda

# Fast path: tests only
.PHONY: fast
fast:
	@$(MAKE) tests AGDA_FLAGS="$(AGDA_FLAGS_FAST)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS_FAST)"

docs: doc-reference-check check-all-docs

docs-curated: doc-reference-check
	$(AGDA) $(AGDA_CI_FLAGS) docs/Library.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/LogOS_Overview.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/Architecture_PortsAdapters.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/LogOS_Core_Spec.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/Communication.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/AIAssistedModeling.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/DeepDive/CoreScience.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Views/All.lagda.md
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

sync-license-headers:
	@bash scripts/sync_license_headers.sh

ci-workflow-policy-check:
	@bash scripts/ci_workflow_policy_check.sh

honesty-check:
	@bash scripts/honesty_check.sh

postulate-policy-check:
	@bash scripts/postulate_policy_check.sh

safe-options-check:
	@bash scripts/safe_options_check.sh

host-surface-check:
	@bash scripts/host_surface_check.sh

host-import-check:
	@bash scripts/host_import_check.sh

minimal-api-no-axioms-check:
	@bash scripts/minimal_api_no_axioms_check.sh

api-no-axioms-check:
	@bash scripts/api_no_axioms_check.sh

pack-trust-check:
	@bash scripts/pack_trust_check.sh

readme-pack-trust-check:
	@bash scripts/readme_pack_trust_check.sh

agda-lib-policy-check:
	@bash scripts/agda_lib_policy_check.sh

import-layer-check:
	@bash scripts/import_layer_check.sh

layer-order-check:
	@bash scripts/layer_order_check.sh

operational-no-theorems-imports-check:
	@bash scripts/operational_no_theorems_imports_check.sh

topic-kernel-api-check:
	@bash scripts/topic_kernel_api_check.sh

topic-all-index-check:
	@bash scripts/topic_all_index_check.sh

demo-isolation-check:
	@bash scripts/demo_isolation_check.sh

sketch-location-check:
	@bash scripts/sketch_location_check.sh

no-tabs-check:
	@bash scripts/no_tabs_check.sh

dangerous-pragmas-check:
	@bash scripts/dangerous_pragmas_check.sh

stable-surface-no-experimental-imports-check:
	@bash scripts/stable_surface_no_experimental_imports_check.sh

stable-surface-no-guardless-exports-check:
	@bash scripts/stable_surface_no_guardless_exports_check.sh

stable-surface-no-internal-mu-imports-check:
	@bash scripts/stable_surface_no_internal_mu_imports_check.sh

stable-surface-no-kernel-io-imports-check:
	@bash scripts/stable_surface_no_kernel_io_imports_check.sh

stable-surface-no-domain-imports-check:
	@bash scripts/stable_surface_no_domain_imports_check.sh

stable-surface-no-meta-assumption-imports-check:
	@bash scripts/stable_surface_no_meta_assumption_imports_check.sh

stable-surface-no-banned-transitive-imports-check:
	@bash scripts/stable_surface_no_banned_transitive_imports_check.sh

stable-surface-lock-check:
	@bash scripts/stable_surface_lock_check.sh

mk-satsystem-policy-check:
	@bash scripts/mk_satsystem_policy_check.sh

relation-symbol-governance-check:
	@bash scripts/relation_symbol_governance_check.sh

doc-style-lint-check:
	@bash scripts/doc_style_lint_check.sh

claim-stamp-check:
	@bash scripts/claim_stamp_check.sh

doc-analogy-markers-check:
	@bash scripts/doc_analogy_markers_check.sh

doc-internal-imports-check:
	@bash scripts/doc_internal_imports_check.sh

bad-code-smells-check:
	@bash scripts/bad_code_smells_check.sh

doc-reference-check:
	@bash scripts/doc_reference_check.sh

doc-module-check: doc-reference-check
	@bash scripts/doc_module_check.sh

surface-namespace-check:
	@bash scripts/surface_namespace_check.sh

assumption-boundary-check:
	@bash scripts/assumption_boundary_check.sh

assumptions-ledger-check:
	@bash scripts/assumptions_ledger_check.sh

reachability-check:
	@bash scripts/reachability_check.sh

agda-lib-check:
	@echo "Agda library-file smoke test (LogOS.agda-lib)..."
	@mkdir -p _build
	@printf '%s\n' "$(CURDIR)/LogOS.agda-lib" > _build/local.agda-libraries
	$(AGDA) --no-default-libraries --library-file=_build/local.agda-libraries -l LogOS --safe $(AGDA_WARN_FLAGS) LogOS/API/Minimal.agda

ci-policy: license-check license-headers-check ci-workflow-policy-check honesty-check postulate-policy-check safe-options-check host-surface-check host-import-check minimal-api-no-axioms-check api-no-axioms-check pack-trust-check readme-pack-trust-check agda-lib-policy-check import-layer-check layer-order-check operational-no-theorems-imports-check topic-kernel-api-check topic-all-index-check demo-isolation-check sketch-location-check no-tabs-check dangerous-pragmas-check stable-surface-no-experimental-imports-check stable-surface-no-guardless-exports-check stable-surface-no-internal-mu-imports-check stable-surface-no-kernel-io-imports-check stable-surface-no-domain-imports-check stable-surface-no-meta-assumption-imports-check stable-surface-no-banned-transitive-imports-check stable-surface-lock-check mk-satsystem-policy-check relation-symbol-governance-check doc-style-lint-check claim-stamp-check doc-analogy-markers-check doc-internal-imports-check bad-code-smells-check doc-reference-check doc-module-check surface-namespace-check kernel-antisymmetry-check assumption-boundary-check assumptions-ledger-check reachability-check lint

ci: ci-policy vacuity-check correctness-check tests examples docs

kernel-antisymmetry-check:
	@bash scripts/kernel_antisymmetry_check.sh

vacuity-check:
	$(AGDA) $(AGDA_CI_FLAGS) Tests/Vacuity.agda

correctness-check:
	$(AGDA) $(AGDA_CI_FLAGS) Tests/Correctness.agda

## Optional: type-check curated packs (heavier; not part of `ci` by default)
packs: packs-zfc packs-universality packs-opacity packs-complexity packs-agents

packs-strict: packs

packs-zfc:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Packs/ZFC/All.agda

packs-universality:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Packs/Universality/All.agda

packs-opacity:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Packs/Opacity/Experimental/All.agda

packs-complexity:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Packs/Complexity/Experimental/All.agda

packs-agents:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Packs/Agents/All.agda

lint:
	@bash scripts/banned_imports_lint.sh

shellcheck:
	@shellcheck -x scripts/*.sh scripts/lib/*.sh

# Publication sanity: type-check every Agda source file in this repo.
#
# Note: this is intentionally heavier than `make ci` (which checks curated entrypoints).
check-quick: ci-policy check-all-agda agda-lib-check

check-quick-no-transformer:
	@$(MAKE) check-quick PIPELINE_SKIP=1

check-all-warm: ci-policy check-all-agda check-all-docs agda-lib-check

check-all: clean check-all-warm

check-all-clean: check-all

# Readability alias: "make-all" = full publication sanity check.
make-all: check-all

check-all-agda:
	@echo "Type-checking all *.agda files..."
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" PIPELINE_PROFILE="$(PIPELINE_PROFILE)" PIPELINE_SKIP="$(PIPELINE_SKIP)" \
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
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/LogOS_Overview.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/Architecture_PortsAdapters.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/LogOS_Core_Spec.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/All.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/HoTT_3Level.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/CategoricalLogic.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/MultiInstitution.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/ObserverSemantics.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/CurryHowardLambek.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Views/MeredithSentences.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/ZFC.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/CoreScience.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/Communication.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/AIAssistedModeling.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/PLSpine.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/ZFC_Demo.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/DeepDive/Complexity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Opacity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Complexity.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Universality.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/InfoTheory.lagda.md
	$(AGDA) $(AGDA_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Applications/Agents.lagda.md
	@bash scripts/write_html_index.sh "$(HTML_DIR)"

depgraph:
	@python3 scripts/depgraph.py --render
