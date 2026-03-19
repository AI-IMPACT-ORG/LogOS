# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
#
# Minimal build harness for the 1.1 logical-transformer core.
#
# Guardrails:
# - stdlib-independent build (`--no-libraries`)
# - safe mode (`--safe`) across the checked surface
# - no K axiom (`--without-K`) across the checked surface
# - strict warnings (`-W all -W error`)

AGDA ?= agda

# Toolchain note:
# - Locally, `AGDA` is resolved via PATH unless overridden.
# - CI installs a pinned Agda via cabal (see `.github/workflows/ci.yml` and
#   `.github/cabal-index-state.txt`).
# - Warnings like `CoverageNoExactSplit` are emitted by Agda itself, so when one
#   appears, first confirm which toolchain is in use:
#     agda --version
#     agda --print-agda-dir

AGDA_FLAGS_BASE ?= --no-libraries -i . --safe --without-K
AGDA_FLAGS ?= $(AGDA_FLAGS_BASE)
AGDA_HYGIENE_LINE_LIMIT ?= 700

# Keep strict warnings enabled.
#
# Note: if `CoverageNoExactSplit` fires, treat it as a real signal: Agda's exact
# split checks failed for some definition. Prefer refactoring the offending
# definition over silencing the warning class.
AGDA_WARN_FLAGS ?= -W all -W error

AGDA_CI_FLAGS ?= $(AGDA_FLAGS) $(AGDA_WARN_FLAGS)

RE_INTEGRATION_ADAPTERS := ^LogOS\.Adapters\.
RE_INTEGRATION_APPS_INCLUDE := ^LogOS\.Apps\.
RE_INTEGRATION_APPS_EXCLUDE := ^LogOS\.Apps\.ZFC(\.|$$)
RE_ZFC_STACK_CORE := ^LogOS\.Apps\.ZFC\.(Stack($$|\.)|SetTheory\.)
RE_ZFC_MODELS_HIERARCHY := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(CanonicalBridge|CumulativeHierarchy|Hierarchy|HierarchyCompletion|HierarchyCore|HierarchyInfinity)$$
RE_ZFC_MODELS_SUPPORT := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(Context|GeneratedImage|GeneratedSubtree|PresentationAdapters|Rank|StageSetup|StagedReification|SuccessorTruthLift|WellFounded)$$
RE_ZFC_MODELS_SURFACE := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(CuratedSurface|TwoRungSliceSurface)$$
RE_ZFC_MODELS_SEMANTICS_STAGE := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(SemanticsStage)$$
RE_ZFC_MODELS_SEMANTICS_CANONICAL := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(Semantics|SemanticsCanonical)$$
RE_ZFC_MODELS_SEMANTICS_COMPLETION_BASE := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(CompletionAtStage|CompletionAtStageSemantics|CumulativeHierarchyCompletion|CumulativeHierarchyCurrentCompletion|CumulativeHierarchyCurrentCompletionSemantics|LateCollapseAssumptions|SemanticsCompletion|SemanticsCurrentCompletion|SemanticsCurrentCompletionSemantics)$$
RE_ZFC_MODELS_SEMANTICS_COMPLETION_SUCCESSOR := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(CumulativeHierarchySuccessorCompletion|CumulativeHierarchySuccessorCompletionSemantics|SemanticsSuccessorCompletion|SemanticsSuccessorCompletionSemantics)$$
RE_ZFC_MODELS_SEMANTICS_COMPLETION_RANK := ^LogOS\.Apps\.ZFC\.Models\.IterativeSetTree\.(RankBoundedFO)$$
RE_ZFC_PROOF := ^LogOS\.Apps\.ZFC\.Proof($$|\.)
RE_ZFC_METAMATH := ^LogOS\.Apps\.ZFC\.Metamath($$|\.)
RE_ZFC_SURFACE := ^LogOS\.Apps\.ZFC\.(All|PackSurface|MetamathSurface)$$
RE_DOCS_CORE := ^docs\.Core\.
RE_DOCS_PATTERNS_BASE := ^docs\.Patterns\.
RE_DOCS_PATTERNS_BASE_EXCLUDE := ^docs\.Patterns\.Examples\.
RE_DOCS_PATTERNS_EXAMPLES := ^docs\.Patterns\.Examples\.
RE_DOCS_PATTERNS_EXAMPLES_EXCLUDE := ^docs\.Patterns\.Examples\.Example_AbstractDeutsch_Category_ZFC$$
RE_DOCS_INTERPRETATIONS_BASE := ^docs\.Interpretations\.
RE_DOCS_INTERPRETATIONS_BASE_EXCLUDE := ^docs\.Interpretations\.(Applications\.ZFC_Curated_Surface|Applications\.ZFC_Two_Rung_Cumulative_Hierarchy|Orientation\.ZFC_Quickstart)$$
RE_DOCS_ZFC_QUICKSTART := ^docs\.Interpretations\.Orientation\.ZFC_Quickstart$$
RE_DOCS_ZFC_SURFACE := ^docs\.Interpretations\.Applications\.ZFC_Curated_Surface$$
RE_DOCS_ZFC_HIERARCHY := ^docs\.Interpretations\.Applications\.ZFC_Two_Rung_Cumulative_Hierarchy$$
RE_DOCS_ZFC_PATTERNS := ^docs\.Patterns\.Examples\.Example_AbstractDeutsch_Category_ZFC$$
RE_DOCS_RESULTS := ^docs\.Results\.

.PHONY: help clean
.PHONY: agda-toolchain
.PHONY: toolchain-check
.PHONY: check check-docs-core check-docs check-ports check-apps
.PHONY: check-policy check-core check-integration check-lib
.PHONY: check-core-agda check-integration-agda check-all-agda check-all-docs agda-lib-check
.PHONY: check-core-agda-telemetry check-integration-agda-telemetry check-all-agda-telemetry check-all-docs-telemetry
.PHONY: check-integration-agda-monolithic check-all-agda-monolithic check-all-docs-monolithic
.PHONY: check-integration-adapters-agda check-integration-apps-agda
.PHONY: check-integration-zfc-stack-agda check-integration-zfc-stack-core-agda
.PHONY: check-integration-zfc-models-structure-agda check-integration-zfc-models-hierarchy-agda
.PHONY: check-integration-zfc-models-support-agda check-integration-zfc-models-surface-agda
.PHONY: check-integration-zfc-models-semantics-agda check-integration-zfc-models-semantics-stage-agda
.PHONY: check-integration-zfc-models-semantics-canonical-agda check-integration-zfc-models-semantics-completion-agda
.PHONY: check-integration-zfc-models-semantics-completion-base-agda check-integration-zfc-models-semantics-completion-successor-agda check-integration-zfc-models-semantics-completion-rank-agda
.PHONY: check-integration-zfc-proof-agda
.PHONY: check-integration-zfc-metamath-agda check-integration-zfc-surface-agda
.PHONY: check-integration-adapters-agda-telemetry check-integration-apps-agda-telemetry
.PHONY: check-integration-zfc-stack-agda-telemetry check-integration-zfc-stack-core-agda-telemetry
.PHONY: check-integration-zfc-models-structure-agda-telemetry check-integration-zfc-models-hierarchy-agda-telemetry
.PHONY: check-integration-zfc-models-support-agda-telemetry check-integration-zfc-models-surface-agda-telemetry
.PHONY: check-integration-zfc-models-semantics-agda-telemetry check-integration-zfc-models-semantics-stage-agda-telemetry
.PHONY: check-integration-zfc-models-semantics-canonical-agda-telemetry check-integration-zfc-models-semantics-completion-agda-telemetry
.PHONY: check-integration-zfc-models-semantics-completion-base-agda-telemetry check-integration-zfc-models-semantics-completion-successor-agda-telemetry check-integration-zfc-models-semantics-completion-rank-agda-telemetry
.PHONY: check-integration-zfc-proof-agda-telemetry
.PHONY: check-integration-zfc-metamath-agda-telemetry check-integration-zfc-surface-agda-telemetry
.PHONY: check-all-docs-core-tree check-all-docs-patterns-base check-all-docs-patterns-examples
.PHONY: check-all-docs-interpretations-base check-all-docs-zfc check-all-docs-zfc-quickstart
.PHONY: check-all-docs-zfc-surface check-all-docs-zfc-hierarchy check-all-docs-zfc-patterns check-all-docs-results
.PHONY: check-all-docs-core-tree-telemetry check-all-docs-patterns-base-telemetry check-all-docs-patterns-examples-telemetry
.PHONY: check-all-docs-interpretations-base-telemetry check-all-docs-zfc-telemetry check-all-docs-zfc-quickstart-telemetry
.PHONY: check-all-docs-zfc-surface-telemetry check-all-docs-zfc-hierarchy-telemetry check-all-docs-zfc-patterns-telemetry check-all-docs-results-telemetry
.PHONY: check_against_std_lib check_against_cubical_lib
.PHONY: license-check license-headers-check ci-workflow-policy-check
.PHONY: safe-options-check unsafe-options-check dangerous-pragmas-check no-with-k-check
.PHONY: host-surface-check host-import-check postulate-policy-check
.PHONY: agda-lib-policy-check doc-reference-check layer-order-check spec-ref-check
.PHONY: claim-stamp-check api-purity-check policy-coverage-check proof-coverage-check law-surface-check coherence-law-check
.PHONY: stale-allowlists-check agda-policy-bundle-check agda-hygiene-check no-redundant-hiding-check
.PHONY: trivial-boundary-smell-check
.PHONY: theorems-catalog-check
.PHONY: pack-story-contract-check doc-import-discipline-check reachability-check
.PHONY: zfc-canonical-slice-purity-check zfc-canonical-bridge-purity-check zfc-legacy-quarantine-check zfc-bridge-slice-compile-check
.PHONY: makefile-guardrails-check check-scripts-meta-policy-check no-tabs-check shellcheck
.PHONY: architecture-shim-check architecture-api-surface-check canonical-architecture-import-check legacy-architecture-name-check canonical-legacy-free-check refinement-first-surface-check equality-quarantine-check packaging-equality-check core-role-check type-theory-shell-check lt-theorem-boundary-check
.PHONY: publication-surface-check publication-wording-check publication-default-lane-check publication-generated-index-check
.PHONY: generated-docs-fresh-check
.PHONY: unicode-invisibles-check
.PHONY: local-boundary-usage-check
.PHONY: ports-uniform-import-check
.PHONY: spec-lt-imports
.PHONY: lt-ports-import-graph
.PHONY: views-all design-all
.PHONY: required-docs-check ports-as-displayed-doc-contract-check ports-as-displayed-design-contract-check
.PHONY: no-hidden-decoratedthin2cat-check no-manual-displayed-product-check law-port-forgetfuls-doc-check
.PHONY: abstract-deutsch-doc-contract-check no-cloning-doc-mention-check quarantine-story-doc-check spine-doc-contract-check
.PHONY: root-hygiene-check archive-boundary-check docs-taxonomy-check
.PHONY: curated-docs-index-coverage-check subtree-navigator-check tooling-contract-check
.PHONY: relation-status-naming-check polarity-reminder-check public-portstack-uniqueness-check rewrite-hotspot-check zfc-upgrade-index equality-surface-map strictification-inventory zfc-upgrade-discipline-check
.PHONY: strictification-boundary-check strictification-contract-check shadowing-lane-check strictification-doc-import-check centering-quote-vocabulary-check
.PHONY: architecture-clarity-report architecture-clarity-check
.PHONY: check-core-warm check-integration-warm
.PHONY: ci-policy check-all-warm check-all ci html layer-order-legend module-index policy-index docs-index claim-stamp-index published-surface-index spec-lt-imports lt-ports-import-graph docs-refresh

help:
	@echo "Common targets:"
	@echo "  make agda-toolchain - print Agda toolchain info"
	@echo "  make toolchain-check - verify required tools + print versions"
	@echo "  make check       - quick curated API smoke test"
	@echo "  make check-policy - repository policy + hygiene gate"
	@echo "  make check-core  - core Agda lane"
	@echo "  make check-integration - integration/app Agda lane"
	@echo "  make check-docs  - all literate docs lane"
	@echo "  make check-lib   - agda-lib smoke test"
	@echo "  make check-all   - cold full gate with Agda compile telemetry (clean + policy + all sources)"
	@echo "    optional: AGDA_TIMEOUT_SECS=<n> make check-all"
	@echo "  make check-all-warm - warm full gate with Agda compile telemetry (no clean)"
	@echo "Focused sublanes:"
	@echo "  make check-integration-zfc-stack-agda - focused ZFC stack/model umbrella"
	@echo "  make check-integration-zfc-models-hierarchy-agda - focused ZFC hierarchy hotspot"
	@echo "  make check-integration-zfc-models-semantics-agda - focused ZFC semantics hotspot"
	@echo "  make check-integration-zfc-models-semantics-completion-agda - focused ZFC completion hotspot"
	@echo "  make check-integration-zfc-models-semantics-completion-successor-agda - focused ZFC successor-completion hotspot"
	@echo "  make check-integration-zfc-models-semantics-completion-rank-agda - focused ZFC rank-bounded FO hotspot"
	@echo "  make check-integration-zfc-models-surface-agda - optional ZFC thin surface lane (docs already cover it)"
	@echo "  make check-integration-zfc-proof-agda - focused ZFC proof lane"
	@echo "  make check-all-docs-zfc - focused ZFC docs umbrella"
	@echo "  make check-all-docs-zfc-hierarchy - focused ZFC hierarchy doc"
	@echo "  make check-core-warm - warm core gate"
	@echo "  make check-integration-warm - warm integration gate"
	@echo "  make ci          - warm core CI alias"
	@echo "  make check_against_std_lib    - optional: check LogOS against agda-stdlib (requires AGDA_STDLIB)"
	@echo "  make check_against_cubical_lib - optional: check LogOS against Cubical library (requires AGDA_CUBICAL_LIB)"
	@echo "  make html        - build selected HTML doc entrypoints into _build/html"
	@echo "  make generated-docs-fresh-check - verify generated docs are up to date"
	@echo "  make layer-order-legend - regenerate docs/Generated/Architecture_Layer_Order.md"
	@echo "  make module-index - regenerate docs/Generated/Module_Index.md"
	@echo "  make policy-index - regenerate docs/Generated/Policy_Index.md"
	@echo "  make docs-index - regenerate docs/Generated/Docs_Index.md"
	@echo "  make claim-stamp-index - regenerate docs/Generated/Claim_Stamp_Index.md"
	@echo "  make published-surface-index - regenerate docs/Generated/Published_Surface_Index.md"
	@echo "  make zfc-upgrade-index - regenerate docs/Generated/ZFC_Upgrade_Index.md"
	@echo "  make equality-surface-map - regenerate docs/Generated/Equality_Surface_Map.md"
	@echo "  make strictification-inventory - regenerate docs/Generated/Strictification_Inventory.md"
	@echo "  make views-all - regenerate docs/Interpretations/Views/All.lagda.md"
	@echo "  make design-all - regenerate docs/Patterns/All.lagda.md"
	@echo "  make architecture-clarity-report - regenerate docs/Generated/Architecture_Clarity_Index.md"
	@echo "  make architecture-clarity-check - run architecture shim/API/import/legacy checks"
	@echo "  make proof-coverage-check - report host mechanization and assumption-light CI metrics"
	@echo "  make law-surface-check - report heuristic explicit-law Agda surface metrics"
	@echo "  make coherence-law-check - report mode-indexed-law coverage and relation-split duplication risk"
	@echo "  make packaging-equality-check - ban leaked template packaging equalities outside quarantine lanes"
	@echo "  make core-role-check - ban Core modules from importing Definitional/Strictification lanes unless allowlisted"
	@echo "  make type-theory-shell-check - keep non-quarantine TypeTheory modules as re-export shells"
	@echo "  make spec-lt-imports - regenerate LT import block in docs/Core/Spec/LogicalTransformers.lagda.md"
	@echo "  make lt-ports-import-graph - regenerate docs/Generated/LT_Ports_Import_Graph.md"
	@echo "  make docs-refresh - regenerate indexes/spec imports/import graph, then build selected HTML doc entrypoints"
	@echo "  make shellcheck  - run shellcheck over scripts/"
	@echo "  make clean       - remove .agdai/.agda.err, macOS zip artifacts, and _build/"

clean:
	@echo "Cleaning Agda artifacts..."
	@find . -type f -name '*.agdai' -delete 2>/dev/null || true
	@find . -type f -name '*.agda.err' -delete 2>/dev/null || true
	@find . -type f -name '*.pyc' -delete 2>/dev/null || true
	@find . -type d -name '__pycache__' -prune -exec rm -rf {} + 2>/dev/null || true
	@find . -type f -name '._*' -delete 2>/dev/null || true
	@find . -type f -name '.DS_Store' -delete 2>/dev/null || true
	@find . -type d -name '__MACOSX' -prune -exec rm -rf {} + 2>/dev/null || true
	@rm -rf _build

agda-toolchain:
	@echo "Agda toolchain (as invoked by make):"
	@echo "  AGDA=$(AGDA)"
	@$(AGDA) --version
	@$(AGDA) --print-agda-dir

toolchain-check:
	@bash scripts/check_env.sh

check:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/API/LT.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Checks/ExtensionalityLadder.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Checks/Conventions/All.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Checks/PortStackUniquePublic.agda

check-docs-core:
	$(AGDA) $(AGDA_CI_FLAGS) docs/Core/Orientation/LogOS_Overview.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Core/Spec/LogOS_Specification.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) docs/Core/Spec/LogicalTransformers.lagda.md

check-ports:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Ports/Opacity.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Ports/IO.agda

check-apps:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Apps/Opacity/Demo.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Apps/ZFC/Stack.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Apps/ZFC/Proof.agda
	@$(MAKE) zfc-bridge-slice-compile-check

# Optional: consistency checks against external libraries.
#
# Policy rule: these must remain non-load-bearing for the LogOS core.
# The check modules are generated under `_build/**` by the runner scripts, so
# the default gates remain stdlib-free (`--no-libraries`).

check_against_std_lib:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_against_std_lib.sh

check_against_cubical_lib:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_against_cubical_lib.sh

check-core-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_core_agda.sh

check-integration-agda-monolithic:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_integration_agda.sh

check-all-agda-monolithic:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_all_agda.sh

check-core-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		bash scripts/check_core_agda.sh

check-integration-agda-monolithic-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		bash scripts/check_integration_agda.sh

check-all-agda-monolithic-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		bash scripts/check_all_agda.sh

check-all-docs-monolithic:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		bash scripts/check_all_docs.sh

check-all-docs-monolithic-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		bash scripts/check_all_docs.sh

check-integration-adapters-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_INTEGRATION_ADAPTERS)' \
		bash scripts/check_integration_agda.sh

check-integration-adapters-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_INTEGRATION_ADAPTERS)' \
		bash scripts/check_integration_agda.sh

check-integration-apps-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_INTEGRATION_APPS_INCLUDE)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_INTEGRATION_APPS_EXCLUDE)' \
		bash scripts/check_integration_agda.sh

check-integration-apps-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_INTEGRATION_APPS_INCLUDE)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_INTEGRATION_APPS_EXCLUDE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-stack-core-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_STACK_CORE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-stack-core-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_STACK_CORE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-hierarchy-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_HIERARCHY)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-hierarchy-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_HIERARCHY)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-support-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SUPPORT)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-support-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SUPPORT)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-surface-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SURFACE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-surface-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SURFACE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-structure-agda: check-integration-zfc-models-hierarchy-agda check-integration-zfc-models-support-agda

check-integration-zfc-models-structure-agda-telemetry: check-integration-zfc-models-hierarchy-agda-telemetry check-integration-zfc-models-support-agda-telemetry

check-integration-zfc-models-semantics-stage-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_STAGE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-stage-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_STAGE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-canonical-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_CANONICAL)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-canonical-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_CANONICAL)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-base-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_COMPLETION_BASE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-base-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_COMPLETION_BASE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-successor-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_COMPLETION_SUCCESSOR)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-successor-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_COMPLETION_SUCCESSOR)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-rank-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_COMPLETION_RANK)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-rank-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_MODELS_SEMANTICS_COMPLETION_RANK)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-models-semantics-completion-agda: check-integration-zfc-models-semantics-completion-base-agda check-integration-zfc-models-semantics-completion-successor-agda check-integration-zfc-models-semantics-completion-rank-agda

check-integration-zfc-models-semantics-completion-agda-telemetry: check-integration-zfc-models-semantics-completion-base-agda-telemetry check-integration-zfc-models-semantics-completion-successor-agda-telemetry check-integration-zfc-models-semantics-completion-rank-agda-telemetry

check-integration-zfc-models-semantics-agda: check-integration-zfc-models-semantics-stage-agda check-integration-zfc-models-semantics-canonical-agda check-integration-zfc-models-semantics-completion-agda

check-integration-zfc-models-semantics-agda-telemetry: check-integration-zfc-models-semantics-stage-agda-telemetry check-integration-zfc-models-semantics-canonical-agda-telemetry check-integration-zfc-models-semantics-completion-agda-telemetry

check-integration-zfc-stack-agda: check-integration-zfc-stack-core-agda check-integration-zfc-models-structure-agda check-integration-zfc-models-semantics-agda

check-integration-zfc-stack-agda-telemetry: check-integration-zfc-stack-core-agda-telemetry check-integration-zfc-models-structure-agda-telemetry check-integration-zfc-models-semantics-agda-telemetry

check-integration-zfc-proof-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_PROOF)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-proof-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_PROOF)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-metamath-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_METAMATH)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-metamath-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_METAMATH)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-surface-agda:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_SURFACE)' \
		bash scripts/check_integration_agda.sh

check-integration-zfc-surface-agda-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_ZFC_SURFACE)' \
		bash scripts/check_integration_agda.sh

check-integration-agda: check-integration-adapters-agda check-integration-apps-agda check-integration-zfc-stack-agda check-integration-zfc-proof-agda check-integration-zfc-metamath-agda check-integration-zfc-surface-agda

check-integration-agda-telemetry: check-integration-adapters-agda-telemetry check-integration-apps-agda-telemetry check-integration-zfc-stack-agda-telemetry check-integration-zfc-proof-agda-telemetry check-integration-zfc-metamath-agda-telemetry check-integration-zfc-surface-agda-telemetry

check-all-docs-core-tree:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_CORE)' \
		bash scripts/check_all_docs.sh

check-all-docs-core-tree-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_CORE)' \
		bash scripts/check_all_docs.sh

check-all-docs-patterns-base:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_PATTERNS_BASE)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_DOCS_PATTERNS_BASE_EXCLUDE)' \
		bash scripts/check_all_docs.sh

check-all-docs-patterns-base-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_PATTERNS_BASE)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_DOCS_PATTERNS_BASE_EXCLUDE)' \
		bash scripts/check_all_docs.sh

check-all-docs-patterns-examples:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_PATTERNS_EXAMPLES)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_DOCS_PATTERNS_EXAMPLES_EXCLUDE)' \
		bash scripts/check_all_docs.sh

check-all-docs-patterns-examples-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_PATTERNS_EXAMPLES)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_DOCS_PATTERNS_EXAMPLES_EXCLUDE)' \
		bash scripts/check_all_docs.sh

check-all-docs-interpretations-base:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_INTERPRETATIONS_BASE)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_DOCS_INTERPRETATIONS_BASE_EXCLUDE)' \
		bash scripts/check_all_docs.sh

check-all-docs-interpretations-base-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_INTERPRETATIONS_BASE)' \
		AGDA_CHECK_EXCLUDE_RE='$(RE_DOCS_INTERPRETATIONS_BASE_EXCLUDE)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-quickstart:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_QUICKSTART)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-quickstart-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_QUICKSTART)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-surface:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_SURFACE)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-surface-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_SURFACE)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-hierarchy:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_HIERARCHY)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-hierarchy-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_HIERARCHY)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-patterns:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_PATTERNS)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc-patterns-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_ZFC_PATTERNS)' \
		bash scripts/check_all_docs.sh

check-all-docs-zfc: check-all-docs-zfc-quickstart check-all-docs-zfc-surface check-all-docs-zfc-hierarchy check-all-docs-zfc-patterns

check-all-docs-zfc-telemetry: check-all-docs-zfc-quickstart-telemetry check-all-docs-zfc-surface-telemetry check-all-docs-zfc-hierarchy-telemetry check-all-docs-zfc-patterns-telemetry

check-all-docs-results:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_RESULTS)' \
		bash scripts/check_all_docs.sh

check-all-docs-results-telemetry:
	@AGDA="$(AGDA)" AGDA_FLAGS="$(AGDA_FLAGS)" AGDA_WARN_FLAGS="$(AGDA_WARN_FLAGS)" AGDA_TELEMETRY=1 \
		AGDA_CHECK_INCLUDE_RE='$(RE_DOCS_RESULTS)' \
		bash scripts/check_all_docs.sh

check-all-docs: check-all-docs-core-tree check-all-docs-patterns-base check-all-docs-patterns-examples check-all-docs-interpretations-base check-all-docs-zfc check-all-docs-results

check-all-docs-telemetry: check-all-docs-core-tree-telemetry check-all-docs-patterns-base-telemetry check-all-docs-patterns-examples-telemetry check-all-docs-interpretations-base-telemetry check-all-docs-zfc-telemetry check-all-docs-results-telemetry

check-all-agda: check-core-agda check-integration-agda

check-all-agda-telemetry: check-core-agda-telemetry check-integration-agda-telemetry

agda-lib-check:
	@echo "Agda library-file smoke test (LogOS.agda-lib)..."
	@mkdir -p _build
	@printf '%s\n' "$(CURDIR)/LogOS.agda-lib" > _build/local.agda-libraries
	$(AGDA) --no-default-libraries --library-file=_build/local.agda-libraries -l LogOS-LT --safe --without-K $(AGDA_WARN_FLAGS) LogOS/API/LT.agda

no-with-k-check:
	@bash scripts/check/no_with_k_check.sh

check-policy: ci-policy

check-core: check-core-agda

check-integration: check-integration-agda

check-docs: check-all-docs

check-lib: agda-lib-check

license-check:
	@bash scripts/check_gplv3_notice.sh

license-headers-check:
	@bash scripts/check/license_headers_check.sh

ci-workflow-policy-check:
	@bash scripts/check/ci_workflow_policy_check.sh

makefile-guardrails-check:
	@bash scripts/check/makefile_guardrails_check.sh

safe-options-check:
	@bash scripts/check/safe_options_check.sh

unsafe-options-check:
	@bash scripts/check/unsafe_options_check.sh

dangerous-pragmas-check:
	@bash scripts/check/dangerous_pragmas_check.sh

host-surface-check:
	@bash scripts/check/host_surface_check.sh

host-import-check:
	@bash scripts/check/host_import_check.sh

postulate-policy-check:
	@bash scripts/check/postulate_policy_check.sh

agda-lib-policy-check:
	@bash scripts/check/agda_lib_policy_check.sh

doc-reference-check:
	@bash scripts/check/doc_reference_check.sh

layer-order-check:
	@bash scripts/check/layer_order_check.sh

spec-ref-check:
	@bash scripts/check/spec_ref_check.sh

generated-docs-fresh-check:
	@bash scripts/check/generated_docs_fresh_check.sh

unicode-invisibles-check:
	@bash scripts/check/unicode_invisibles_check.sh

architecture-shim-check:
	@bash scripts/check/architecture_shim_check.sh

architecture-api-surface-check:
	@bash scripts/check/architecture_api_surface_check.sh

canonical-architecture-import-check:
	@bash scripts/check/canonical_architecture_import_check.sh

legacy-architecture-name-check:
	@bash scripts/check/legacy_architecture_name_check.sh

canonical-legacy-free-check:
	@bash scripts/check/canonical_legacy_free_check.sh

refinement-first-surface-check:
	@bash scripts/check/refinement_first_surface_check.sh

equality-quarantine-check:
	@bash scripts/check/equality_quarantine_check.sh

publication-surface-check:
	@bash scripts/check/publication_surface_check.sh

publication-wording-check:
	@bash scripts/check/publication_wording_check.sh

publication-default-lane-check:
	@bash scripts/check/publication_default_lane_check.sh

publication-generated-index-check:
	@bash scripts/check/publication_generated_index_check.sh

packaging-equality-check:
	@bash scripts/check/packaging_equality_check.sh

core-role-check:
	@bash scripts/check/core_role_check.sh

type-theory-shell-check:
	@bash scripts/check/type_theory_shell_check.sh

claim-stamp-check:
	@bash scripts/check/claim_stamp_check.sh

api-purity-check:
	@bash scripts/check/api_purity_check.sh

atomic-spine-import-check:
	@bash scripts/check/atomic_spine_import_check.sh

theorems-catalog-check:
	@bash scripts/check/theorems_catalog_check.sh

lt-theorem-boundary-check:
	@bash scripts/check/lt_theorem_boundary_check.sh

strictification-boundary-check:
	@bash scripts/check/strictification_boundary_check.sh

strictification-contract-check:
	@bash scripts/check/strictification_contract_check.sh

ports-as-displayed-coverage-check:
	@bash scripts/check/ports_as_displayed_coverage_check.sh

required-docs-check:
	@bash scripts/check/required_docs_check.sh

ports-as-displayed-doc-contract-check:
	@bash scripts/check/ports_as_displayed_doc_contract_check.sh

ports-as-displayed-design-contract-check:
	@bash scripts/check/ports_as_displayed_design_contract_check.sh

no-hidden-decoratedthin2cat-check:
	@bash scripts/check/no_hidden_decoratedthin2cat_check.sh

no-manual-displayed-product-check:
	@bash scripts/check/no_manual_displayed_product_check.sh

law-port-forgetfuls-doc-check:
	@bash scripts/check/law_port_forgetfuls_doc_check.sh

root-hygiene-check:
	@bash scripts/check/root_hygiene_check.sh

no-cloning-doc-mention-check:
	@bash scripts/check/no_cloning_doc_mention_check.sh

quarantine-story-doc-check:
	@bash scripts/check/quarantine_story_doc_check.sh

spine-doc-contract-check:
	@bash scripts/check/spine_doc_contract_check.sh

abstract-deutsch-doc-contract-check:
	@bash scripts/check/abstract_deutsch_doc_contract_check.sh

local-boundary-map-check:
	@bash scripts/check/local_boundary_map_check.sh

local-boundary-usage-check:
	@bash scripts/check/local_boundary_usage_check.sh

agda-policy-bundle-check:
	@bash scripts/check/agda_policy_bundle_check.sh

agda-hygiene-check:
	@AGDA_HYGIENE_LINE_LIMIT="$(AGDA_HYGIENE_LINE_LIMIT)" bash scripts/check/agda_hygiene_check.sh

no-redundant-hiding-check:
	@bash scripts/check/no_redundant_hiding_check.sh

trivial-boundary-smell-check:
	@bash scripts/check/trivial_boundary_smell_check.sh

ports-uniform-import-check:
	@bash scripts/check/ports_uniform_import_check.sh

log-basis-usage-check:
	@bash scripts/check/log_basis_usage_check.sh

quarantine-import-check:
	@bash scripts/check/quarantine_import_check.sh

policy-coverage-check:
	@bash scripts/check/policy_coverage_check.sh

proof-coverage-check:
	@bash scripts/check/proof_coverage_check.sh

law-surface-check:
	@bash scripts/check/law_surface_check.sh

coherence-law-check:
	@bash scripts/check/coherence_law_check.sh

stale-allowlists-check:
	@bash scripts/check/stale_allowlists_check.sh

pack-story-contract-check:
	@bash scripts/check/pack_story_contract_check.sh

doc-import-discipline-check:
	@bash scripts/check/doc_import_discipline_check.sh

design-index-coverage-check:
	@bash scripts/check/design_index_coverage_check.sh

curated-docs-index-coverage-check:
	@bash scripts/check/curated_docs_index_coverage_check.sh

archive-boundary-check:
	@bash scripts/check/archive_boundary_check.sh

docs-taxonomy-check:
	@bash scripts/check/docs_taxonomy_check.sh

subtree-navigator-check:
	@bash scripts/check/subtree_navigator_check.sh

tooling-contract-check:
	@bash scripts/check/tooling_contract_check.sh

reachability-check:
	@bash scripts/check/reachability_check.sh

zfc-canonical-slice-purity-check:
	@bash scripts/check/zfc_canonical_slice_purity_check.sh

zfc-canonical-bridge-purity-check:
	@bash scripts/check/zfc_canonical_bridge_purity_check.sh

zfc-legacy-quarantine-check:
	@bash scripts/check/zfc_legacy_quarantine_check.sh

zfc-bridge-slice-compile-check:
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda
	$(AGDA) $(AGDA_CI_FLAGS) LogOS/Apps/ZFC/Models/IterativeSetTree/CanonicalBridge.agda

check-scripts-meta-policy-check:
	@bash scripts/check/check_scripts_meta_policy_check.sh

no-tabs-check:
	@bash scripts/check/no_tabs_check.sh

shellcheck:
	@shellcheck -x scripts/*.sh scripts/check/*.sh scripts/gen/*.sh scripts/lib/*.sh scripts/metamath/*.sh

ci-policy: license-check license-headers-check ci-workflow-policy-check makefile-guardrails-check check-scripts-meta-policy-check policy-coverage-check proof-coverage-check law-surface-check coherence-law-check stale-allowlists-check no-tabs-check unicode-invisibles-check required-docs-check doc-reference-check generated-docs-fresh-check claim-stamp-check doc-import-discipline-check design-index-coverage-check curated-docs-index-coverage-check archive-boundary-check publication-surface-check publication-wording-check publication-default-lane-check publication-generated-index-check docs-taxonomy-check ports-as-displayed-doc-contract-check ports-as-displayed-design-contract-check no-cloning-doc-mention-check quarantine-story-doc-check spine-doc-contract-check abstract-deutsch-doc-contract-check pack-story-contract-check safe-options-check unsafe-options-check dangerous-pragmas-check no-with-k-check host-surface-check host-import-check postulate-policy-check agda-lib-policy-check layer-order-check atomic-spine-import-check ports-as-displayed-coverage-check no-hidden-decoratedthin2cat-check no-manual-displayed-product-check law-port-forgetfuls-doc-check local-boundary-map-check local-boundary-usage-check agda-policy-bundle-check agda-hygiene-check no-redundant-hiding-check trivial-boundary-smell-check ports-uniform-import-check log-basis-usage-check quarantine-import-check spec-ref-check api-purity-check theorems-catalog-check lt-theorem-boundary-check strictification-boundary-check strictification-contract-check shadowing-lane-check strictification-doc-import-check centering-quote-vocabulary-check reachability-check subtree-navigator-check tooling-contract-check zfc-canonical-slice-purity-check zfc-canonical-bridge-purity-check zfc-legacy-quarantine-check architecture-shim-check architecture-api-surface-check canonical-architecture-import-check legacy-architecture-name-check canonical-legacy-free-check refinement-first-surface-check equality-quarantine-check packaging-equality-check core-role-check type-theory-shell-check root-hygiene-check relation-status-naming-check polarity-reminder-check public-portstack-uniqueness-check rewrite-hotspot-check zfc-upgrade-discipline-check shellcheck

check-core-warm: ci-policy check-core-agda check-docs-core agda-lib-check

check-integration-warm: check-integration-agda

check-all-warm: check-policy check-all-agda-telemetry check-all-docs-telemetry check-lib

ci: check-core-warm

check-all: clean check-all-warm

HTML_DIR ?= _build/html

html: doc-reference-check
	@echo "Building selected HTML doc entrypoints into $(HTML_DIR)..."
	@mkdir -p "$(HTML_DIR)"
	$(AGDA) $(AGDA_CI_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Core/Orientation/LogOS_Overview.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Core/Spec/LogOS_Specification.lagda.md
	$(AGDA) $(AGDA_CI_FLAGS) --html --html-dir="$(HTML_DIR)" docs/Core/Spec/LogicalTransformers.lagda.md
	@bash scripts/gen/write_html_index.sh "$(HTML_DIR)"

layer-order-legend:
	@bash scripts/gen/write_layer_order_legend.sh

module-index:
	@bash scripts/gen/write_module_index.sh

policy-index:
	@bash scripts/gen/write_policy_index.sh

docs-index:
	@bash scripts/gen/write_docs_index.sh

claim-stamp-index:
	@bash scripts/gen/write_claim_stamp_index.sh

published-surface-index:
	@bash scripts/gen/write_published_surface_index.sh

zfc-upgrade-index:
	@python3 -B scripts/generate_zfc_upgrade_index.py docs/Generated/ZFC_Upgrade_Index.md

equality-surface-map:
	@python3 -B scripts/generate_equality_surface_map.py docs/Generated/Equality_Surface_Map.md

strictification-inventory:
	@python3 -B scripts/generate_strictification_inventory.py docs/Generated/Strictification_Inventory.md

views-all:
	@bash scripts/gen/write_views_all.sh

design-all:
	@bash scripts/gen/write_design_all.sh

architecture-clarity-report:
	@bash scripts/gen/write_architecture_clarity_index.sh

architecture-clarity-check: architecture-shim-check architecture-api-surface-check canonical-architecture-import-check legacy-architecture-name-check canonical-legacy-free-check

spec-lt-imports:
	@bash scripts/gen/write_spec_lt_imports.sh

lt-ports-import-graph:
	@bash scripts/gen/write_lt_ports_import_graph.sh

docs-refresh: views-all design-all docs-index module-index policy-index claim-stamp-index published-surface-index zfc-upgrade-index equality-surface-map strictification-inventory architecture-clarity-report spec-lt-imports lt-ports-import-graph html

relation-status-naming-check:
	@bash scripts/check/relation_status_naming_check.sh

polarity-reminder-check:
	@bash scripts/check/polarity_reminder_check.sh

public-portstack-uniqueness-check:
	@bash scripts/check/public_portstack_uniqueness_check.sh

rewrite-hotspot-check:
	@bash scripts/check/rewrite_hotspot_check.sh

zfc-upgrade-discipline-check:
	@bash scripts/check/zfc_upgrade_discipline_check.sh

shadowing-lane-check:
	@bash scripts/check/shadowing_lane_check.sh

strictification-doc-import-check:
	@bash scripts/check/strictification_doc_import_check.sh

centering-quote-vocabulary-check:
	@bash scripts/check/centering_quote_vocabulary_check.sh
