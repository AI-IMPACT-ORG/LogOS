<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% P vs NP via Physical Bottlenecks — LogOS (Conditional)

```agda
module docs.Application_PvsNP where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Models.Complexity.Core
import LogOS.Models.UniversalIR.Core

import LogOS.Domain.Complexity.ProofSearchSeparation
import LogOS.Domain.Complexity.ProofSearchCapstoneGraded
import LogOS.Domain.Complexity.PhysToTruthRouteBridge
import LogOS.Domain.Complexity.PvsNP
import LogOS.Domain.Complexity.ClassicalPvsNP
import LogOS.Domain.Complexity.TruthRoute_Grade_Only

import LogOS.Domain.Complexity.InfoHardnessBridge
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only
import LogOS.Domain.Complexity.PolyGrade
import LogOS.Domain.Complexity.Poly
import LogOS.Domain.Complexity.ProofSearchOpacitySpine
import LogOS.Domain.Complexity.InfoBottleneckAdaptersG
import LogOS.Domain.Complexity.InfoBottleneckAdaptersGraded
import LogOS.Domain.Complexity.Examples.InfoRouteChain
import LogOS.Domain.Complexity.Examples.InfoRouteChainIR
import LogOS.Domain.Complexity.Examples.GoldenPath
import LogOS.Domain.Complexity.Examples.GoldenPathMinsky

import LogOS.Domain.Universality.LCUToLandauer
import LogOS.Domain.Universality.MeasurementCapacity
import LogOS.Domain.Universality.NonUnitaryCapacity
import LogOS.Domain.Universality.InfoProcessingBounds

import LogOS.Domain.UniversalIR.Schemes

import LogOS.Domain.Complexity.Targets.SATPhysicalSeparationCostGuardsGraded
```

> **What this is / isn't**
> - **Not** a ZFC proof of classical P≠NP.
> - **Conditional:** if the stated physical/verification assumptions hold in a model, the separation claim follows.
> - **Generic route:** the graded-flow interface (`DetPolyTimeBoundedG` / `PolyWitnessedTotalVerificationG`) is P/NP-shaped, not language-relative NP.
> **Reviewer quick-check**
> - **Where does hardness come from?** It is an explicit axiom (`InfoHardness` or `ProofLowerBound`), not derived.
> - **Is this classical P≠NP?** No; classical alignment is only via `TruthRoute` + `ClassicalPvsNP`.
> - **What is the minimal meaningful target?** SAT + non-degeneracy laws.

This note is the single, publication-facing entrypoint for the “P vs NP from
physics” story in the production library.

Safe import (curated P/NP surfaces only): `LogOS/Models/Complexity/PvsNP/Public.agda`.

The claim is deliberately **conditional**: LogOS does not assert a proof of
classical P≠NP in ZFC. What it *does* provide is a clean pipeline:

> physically aligned bottleneck axioms + universal computation surface  
> ⇒ a sufficient condition for a separation claim

The `PvsNP` language-relative pack is a **wrapper**: its `Assumptions` already
contain `InNP L` and `¬ InP L`, and `mkPack` only rewraps that data.

Proof-search opacity spine (GRH/opacity core, reused here):
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda`
- This re-exports the spectral/budgeted separation machinery and applies it to
  proof-search oracles, keeping the hardness story non-deterministic.
- Budgets are first-class: use `ProofSearchOpacitySpine.For.Budgeted.GeneralB` to
  swap in any budget carrier (ℕ, quantale scales, physical cost models).

## Two layers: “proof-search separation” and “classical-looking P/NP”

1) **Foundational layer (centerpiece):** verification vs unbounded search under
budgeted classicalization.

- Narrative/theorem surface: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
- Capstone theorem (grade-native core): `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`

2) **Bridge layer:** connect physical “no poly-budget decider” conclusions back
to standard P/NP-style time/correctness predicates.

- Bridge (grade reindexing): `LogOS/Domain/Complexity/PhysToTruthRouteBridge.agda`

For a “strong-by-default” P vs NP surface (correctness-carrying, TM-like), use:

- `LogOS/Domain/Complexity/PvsNP.agda` (packaging of `InNP` + `¬ InP`, no derivation)

For a literature-aligned classical P/NP interface (ℕ-bound compat; cost = time), use:

- `LogOS/Domain/Complexity/ClassicalPvsNP.agda` (namespaced as `LogOS.Models.Complexity.Core.ClassicalPvsNP`)

For the minimal info-theory route (kernel-native, conditional), use:

- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (namespaced as `LogOS.Models.Complexity.Core.PvsNPFromInfo_Grade_Only`)

## The strongest explicit axiom ledger (GRH-aligned style)

You can package the PvsNP-style claim without assuming P != NP by making the
following explicit assumptions in a record (ledger):

1) Diagonalization (metalogical, GRH-style)
   - `TruthDiagonalC Code (WithinBudgetBy ...)`
   - This is the same metalogical assumption used in GRH/opacity; it is explicit.
2) Proof-search oracle (partial, decode-extensional)
   - `ProofSearchOpacitySpine.For.ProofSearchOracle`
   - This does not assume totality.
3) Budget function is decode-extensional
   - `ProofSearchOpacitySpine.For.BudgetBy` (budget + extensionality)
   - Keeps budget discipline aligned with the kernel's decode-equality.
4) Witness cost / physical budget
   - `BudgetedSeparationOutput.WitnessCost`
   - plus a budget function or carrier (via `GeneralB`)
   - This is where "physics-aligned" lives: choose cost = info/energy/irreversible events.
5) Non-vacuity guard (no "all undefined" oracle)
   - `ProofSearchOpacitySpine.For.VacuityGuards` (some code is within budget)
6) Verification is poly-bounded
   - If you want "verification in P", add a polynomial check bound (e.g. via
     `ProofSearchGraded` or `LanguageWitnessW`), and the standard non-degeneracy
     guardrails from `LogOS/Domain/Complexity/StandardCMLaws.agda`.
7) Classical alignment (literature-aligned)
   - Use `LogOS/Domain/Complexity/ClassicalPvsNP.agda` with `QNat` and `gradeBound = τ`
   - This is the explicit alignment bridge to standard time-bound P/NP definitions (cost := time).

All of these are already present as explicit record fields in the codebase; no
hidden postulates.

## What you can actually prove (strongest direct result)

Claim (non-deterministic, LogOS-native):

- Under the ledger above, no proof-search oracle can be total within any
  polynomial budget, while verification remains polynomially checkable.
- This is an internal separation between proof search and proof verification as
  algorithmic tasks, not an outright P != NP claim.

## Guardrails (non-vacuity)

- `LogOS/Domain/Complexity/StandardCMLaws.agda` (`EncodingsInDomain`, `ReasonableSize`)
- `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda` (`NonDegenerate`)
- `LogOS/Domain/Complexity/Examples/GoldenPathMinsky.agda` (`SizeBudget`, `cost≤budget`)
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (`VacuityGuards`)

These keep the ledger honest by ruling out degenerate encodings and vacuous
resource bounds.

## Optional routes and instantiations (tucked away)

- Info‑hardness route (DetBottleneck + InfoHardness):
  `LogOS/Domain/Complexity/InfoHardnessBridge.agda`,
  `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda`
- Physical axiom packs:
  `LogOS/Domain/Universality/LCUToLandauer.agda`,
  `LogOS/Domain/Universality/MeasurementCapacity.agda`,
  `LogOS/Domain/Universality/NonUnitaryCapacity.agda`,
  `LogOS/Domain/Universality/InfoProcessingBounds.agda`
- Classical alignment pipeline:
  `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda` →
  `LogOS/Domain/Complexity/ClassicalPvsNP.agda`
- UniversalIR substrate and examples:
  `LogOS/Domain/UniversalIR/`,
  `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda`,
  `LogOS/Domain/Complexity/Examples/GoldenPath.agda`
- Target example (SAT):
  `LogOS/Domain/Complexity/Targets/SATPhysicalSeparationCostGuardsGraded.agda`
  - Kernel route: `LogOS/Domain/Complexity/Targets/SATPhysicalSeparationCostGuardsGraded.agda` (module Kernel)
- SAT as proof search (proofs = assignments): `LogOS/Domain/Complexity/Targets/SATProofSearch.agda`

## Audit build (one command)

```csh
agda --no-libraries -i . docs/Application_PvsNP.lagda.md
```
