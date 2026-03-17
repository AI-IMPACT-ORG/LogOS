<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Guardrails for AI-assisted development (v1.1)

This repository is designed to be safe to evolve under human–AI collaboration by making *policy executable*:
most architectural and hygiene rules are enforced by CI scripts, not by convention.

Quick start
-----------

- Standard lanes: `make check-policy`, `make check-core`, `make check-integration`,
  `make check-docs`, `make check-lib`
- Cold gate (clean + all lanes): `make check-all`
- AI/LLM hand-off gate: `make check-all`
- Telemetry is part of the default cold gate and hand-off discipline, not a separate optional target.

The telemetry hand-off target writes timestamped module timing TSVs under `_build/telemetry/`.
CI runs `make check-all` and the selected HTML entrypoint build `make html`
(see `.github/workflows/ci.yml`).

Repository lane boundaries are documented in:

- `docs/Core/Project/Repository_Contract.md`

Human–AI collaboration tips
---------------------------

- Treat CI checks as non-negotiable; do not relax invariants to "make CI cheaper."
- Keep semantic claims tied to code anchors or explicit assumptions.
- Do not introduce hidden axioms or implicit dependencies.
- Prefer explicit views/ports to change meaning; do not smuggle semantics into core definitions.
- Verify changes against the guardrails and regenerate generated indexes when required.
- Keep documentation and code consistent; update specs/import blocks when modules move.
- Avoid overpromising: state what is defined, proved, and assumed.
- Use audits: confirm changes against `docs/Generated/Policy_Index.md` and claim stamps.

Agda strictness profile
-----------------------

The default build is intentionally **stdlib-free** and **safe**:

- `--no-libraries -i . --safe` (see `AGDA_FLAGS_BASE` in `Makefile`)
- `-W all -W error` (see `AGDA_WARN_FLAGS` in `Makefile`)

Warnings are treated as real signals. In particular, if `CoverageNoExactSplit` fires, prefer refactoring so
exact split becomes possible instead of silencing the warning class.

Related docs:

- `docs/Core/Policy/Agda_Hygiene.md`
- `docs/Generated/Policy_Index.md` (search for the check name you hit)

Architecture enforcement (selected)
-----------------------------------

The strict, architecture-shaping checks are wired into `make ci-policy` (and therefore into CI):

- Layering: `make layer-order-check` (canonical layer list in `scripts/lib/layers.sh`)
- “No orphan core modules”: `make reachability-check`
- API surface hygiene: `make api-purity-check`
- Host-minimal surface: `make host-surface-check` and `make host-import-check`
- Ports discipline gates: `make ports-as-displayed-coverage-check`, `make quarantine-import-check`,
  `make local-boundary-map-check`

Canonical architecture docs:

- `docs/Core/Architecture/Diagram.lagda.md`
- `docs/Generated/Architecture_Layer_Order.md`
- `docs/Patterns/HowTo/HowTo_Build_Logic_Transformer_Architecture.lagda.md`

Anti-bypass meta-guardrails
---------------------------

The CI harness also defends itself against common “make CI cheaper” anti-patterns:

- Workflow hardening/pinning policy: `scripts/check/ci_workflow_policy_check.sh`
- Makefile strictness invariants: `scripts/check/makefile_guardrails_check.sh`
- “Every check script runs in CI”: `scripts/check/policy_coverage_check.sh`
- “Allowlists stay empty/minimal and justified”: `scripts/check/stale_allowlists_check.sh`

Documentation discipline
------------------------

Public-facing explanations should live in `docs/**`, and key docs are machine-checked (`*.lagda.md`).
Historical material lives in a separate archive outside the live repository surface and is out of contract for it.

If you add or move `LogOS/LT/**/*.agda` modules, keep the spec import block in sync:

- Update `docs/Core/Spec/LogicalTransformers.lagda.md`, or run `make spec-lt-imports`.
