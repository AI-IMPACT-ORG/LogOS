<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Library Overview

```agda
{-# OPTIONS --safe #-}
module docs.Library where

-- Core science “headline” surfaces (small, checked; complexity side still experimental).
import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation as POI
import LogOS.Packs.UniversalIR.Agreement as UAgree
```

This is the landing “library overview” page for the generated HTML docs.

Trust note: each pack surface exposes `packTrust`
(`LogOS/Packs/Trust.agda`) to mark stable vs experimental status
(enforced by `scripts/pack_trust_check.sh`).
The trust taxonomy also includes `scaffold` (demo/wiring, often intentionally
vacuous) and `deprecated` (migration marker; avoid for new work).

Reading discipline (guardrail)
------------------------------
This repo uses a small amount of overloaded terminology. In the docs we try to
separate these meanings explicitly:

- **Literal (checked):** an Agda definition/lemma in the referenced file.
- **Truth after computation (stabilized):** a statement about a closure/fixed
  point (e.g. `Th*`, `Box`, `μ Flow`) — usually only a *lax* fixed point unless
  extra domain structure (ω‑sups, continuity) is assumed.
- **Representational truth (presentation):** a statement transported through
  `decode`/`encode`/`translate`/`SatMor`, i.e. preserved up to the relevant
  satisfaction equivalence; this is not definitional equality.
- **Analogy / interpretation:** physics/CS/maths metaphors (kernel, channel, RG,
  “GRH”, …). These are explicitly labeled as interpretations and do not add
  logical power; the formal content is the cited Agda surface.

Where to start:
- Architecture + entrypoints: `docs/LogOS_Overview.lagda.md`
- Ports/adapters spine: `docs/DeepDive/Architecture_PortsAdapters.lagda.md`
- Kernel claim register (epistemic status of “truth” words): `docs/Kernel/ClaimRegister.lagda.md`
- Research-grade record/law listing: `docs/LogOS_Core_Spec.lagda.md`
- Communication view (boundary/channel framing): `docs/DeepDive/Communication.lagda.md`
- AI-assisted modelling workflow: `docs/DeepDive/AIAssistedModeling.lagda.md`
- PL mechanization spine (syntax/statics/dynamics): `docs/DeepDive/PLSpine.lagda.md`
- Kernel views (same core, different readings): `docs/Views/All.lagda.md`

Stable import surfaces:
- Minimal kernel API: `LogOS/API/Minimal.agda`
- Curated core theorems: `LogOS/Theorems/Core.agda`

Major storylines (docs-first entrypoints):
- ZFC: `docs/Applications/ZFC.lagda.md` (demo: `docs/DeepDive/ZFC_Demo.lagda.md`)
- Complexity (experimental): `docs/DeepDive/Complexity.lagda.md` (application note: `docs/Applications/Complexity.lagda.md`)
- Universality / UniversalIR: `docs/Applications/Universality.lagda.md`
- Opacity / observability (experimental): `docs/Applications/Opacity.lagda.md`
- Information theory (stable): `docs/Applications/InfoTheory.lagda.md`
- Agents (socket + monitoring/auditing): `docs/Applications/Agents.lagda.md`

Curated packs (code-first entrypoints):
- ZFC lock surface: `LogOS/Packs/ZFC/Surface.agda` (umbrella: `LogOS/Packs/ZFC/All.agda`; WFGraph quartets: `LogOS/Packs/ZFC/WFGraph.agda`)
- Universality lock surface: `LogOS/Packs/Universality/Surface.agda` (umbrella: `LogOS/Packs/Universality/All.agda`)
- UniversalIR lock surface: `LogOS/Packs/UniversalIR/Surface.agda` (umbrella: `LogOS/Packs/UniversalIR/All.agda`)
- Opacity lock surface (experimental): `LogOS/Packs/Opacity/Experimental/Surface.agda` (umbrella: `LogOS/Packs/Opacity/Experimental/All.agda`)
- Complexity lock surface (experimental): `LogOS/Packs/Complexity/Experimental/Surface.agda` (umbrella: `LogOS/Packs/Complexity/Experimental/All.agda`)
- Information theory lock surface: `LogOS/Packs/InfoTheory/Surface.agda` (umbrella: `LogOS/Packs/InfoTheory/All.agda`)
- Agents lock surface (stable): `LogOS/Packs/Agents/Surface.agda` (umbrella: `LogOS/Packs/Agents/All.agda`)
- Agents experimental lock surface: `LogOS/Packs/Agents/Experimental/Surface.agda` (umbrella: `LogOS/Packs/Agents/Experimental/All.agda`)

## Core science (checked)

Two small, “headline” results used by the public narrative are typechecked in
CI, but they still live in experimental packs with explicit assumptions.

```agda
open POI public

merge-implies-entropy-increase' : _
merge-implies-entropy-increase' = merge-implies-entropy-increase

irreversible-io-cost-lower-bound' : _
irreversible-io-cost-lower-bound' = irreversible-io-cost-lower-bound

open UAgree public
```
