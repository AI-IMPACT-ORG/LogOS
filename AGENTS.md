<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# AGENTS.md — LogOS (v1.1) contributor instructions

This repo is designed to be friendly to both humans and AI assistants, but it has a few *hard* invariants.

## Design choices

- The mathematics in this repository prefers local refinement over global equality. Always check if a "refined" option is possible - the literature default may be equality, here it is refinement. We try to delay "collapsing" until strictly necessary.
- Equality quarantine is literal: outside `Prelude`, explicit `Definitional` modules, explicit `Strictification` modules, and executable `Checks`, exported `≡`-valued surfaces are not part of the default story. Default LT/API surfaces are refinement-first.
- The goal is a fundamental model of logic, that reproduces many known constructions through polymorphy. Basically the most pristine, compressed model of logic possible (this is why we need refinement)
- We build on weak (i.e. general) foundations, which causes slight generalisations of many known constructions, that can be quietly awesome in various downstream domains
- Dependency injection patterns are used to surface axiom dependency
- Extreme intellectual honesty over axiom dependencies is required, as well as anything else. 
- Mathematical defensive posture: expect extremely pedantic human readers who will pounce on loose wording. If a construction is generalised beyond textbook usage, say so carefully. If textbook concepts are used, check their definitions and usage.



## Hard gates (do not bypass)

- All Agda and literate docs must typecheck under `{-# OPTIONS --safe #-}` with strict warnings.
- No unsolved metas/constraints; no unsafe pragmas; `postulate` only via the explicit allowlist policy.
- Before handing off, run `make check-all`. It is the cold umbrella gate and telemetry is part of the default lane.
- Use `make check-core-warm` for local iteration and `make check-all-warm` when you want the full warm lane without a clean.

## Spec/document sync (important)

The spec sync script requires that the canonical LT spec explicitly import every `LogOS/LT/**/*.agda` module:

- Update `docs/Core/Spec/LogicalTransformers.lagda.md` imports when adding/removing LT modules.
  - Helper: `make spec-lt-imports` regenerates the LT import block.

## Documentation discipline

- Prefer literate docs (`*.lagda.md`) for public-facing explanations.
- Keep docs pedantic: state what is *defined*, what is *proved*, and what is a *design choice*.
- Avoid overpromising: if something is only a scaffold (e.g. Langlands pack), say so and link to the exact code anchors.
- Do not change the main `README.md` without explicit user approval.
- Re-check `docs/Core/Orientation/High_Risk_Conventions.lagda.md` when touching weak/strict semantics, polarity, observational preorders, or ZFC upgrade packaging.

## Codex skills (optional)

If you are running inside a Codex-style harness that supports skills:

- A “skill” is local instructions stored in a `SKILL.md` under `$CODEX_HOME/skills`.
- If a user names a skill, open its `SKILL.md` and follow it.
- Common system skills include `skill-creator` (write/update skills) and `skill-installer` (install skills).
