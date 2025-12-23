<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Complexity — LogOS (Verification vs Search)

```agda
module docs.DeepDive.Complexity where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Models.Complexity.Core
import LogOS.Domain.Complexity.PvsNP
import LogOS.Domain.Complexity.TruthRoute_Grade_Only
import LogOS.Domain.Complexity.TruthRoute
import LogOS.Domain.Complexity.StandardCMLaws
import LogOS.Domain.Complexity.PvsNP_Grade_Only
import LogOS.Domain.Complexity.ClassicalPvsNP
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only
import LogOS.Domain.Complexity.PolyGrade
import LogOS.Domain.Complexity.ProofSearchSeparation
import LogOS.Domain.Complexity.ProofSearchBoundary
import LogOS.Domain.Complexity.ResourceSchemaG
import LogOS.Domain.Complexity.ResourceSchemaGraded
import LogOS.Domain.Complexity.ObservabilityBudgetG
import LogOS.Domain.Complexity.ObservabilityBudgetGraded
import LogOS.Domain.Complexity.ProofSearchOpacitySpine
import LogOS.Domain.Complexity.InfoBottleneckAdaptersG
import LogOS.Domain.Complexity.InfoBottleneckAdaptersGraded
import LogOS.Domain.Complexity.ProofSearchCapstoneGraded
import LogOS.Domain.Complexity.PhysToTruthRouteBridge
import LogOS.Domain.Complexity.Examples.GoldenPath
import LogOS.Domain.Complexity.Examples.GoldenPathMinsky
import LogOS.Domain.Complexity.Targets.ProofSearchChainedTheoremGraded
import LogOS.Domain.Complexity.Targets.ProofSearchQuantumPivotGraded
import LogOS.Domain.Complexity.Targets.ProofSearchGraded
import LogOS.Domain.Complexity.Targets.SATPhysicalSeparationCostGuardsGraded

-- Quantitative “opacity” bridge (budgeted observers/certificates).
import LogOS.Theorems.Meta.BudgetedSeparationOutput
import LogOS.Theorems.Meta.BudgetedTruthPositivity
```

This note is the single, publication-facing entrypoint for the **complexity**
architecture in the production library.

> **What this is / isn't**
> - **Not** a ZFC proof of classical P≠NP.
> - **Conditional:** if the stated assumptions hold in a model, the separation claim follows.
> - **Generic route:** the graded-flow interface (`DetPolyTimeBoundedG` / `PolyWitnessedTotalVerificationG`) is P/NP-shaped, not language-relative NP.

The organizing principle is not “machines first”, but **interfaces first**:
LogOS makes the verification/search boundary explicit and then lets you choose
which computation surface instantiates it (UniversalIR, TMs, circuits, …).

## Core idea: verification is local, search is global

LogOS internalises the split:

- **Verification**: given a candidate certificate/trace, checking is bounded.
- **Search / provability**: deciding existence of some certificate is an
  unbounded existential (a “global OR”), and that is exactly where diagonal /
  observability bottlenecks appear.

This is packaged as the `ProofSearch*` family under `LogOS/Domain/Complexity/*` (with recommended wrappers under `LogOS/Models/Complexity/*`).

## Core ledger (GRH-aligned, proof-search first)

The strongest LogOS-native separation story is *proof-search opacity*:

- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (partial proof-search oracle + budgeted opacity barrier).
- Ledger-style assumptions mirror GRH/opacity: diagonalization (`TruthDiagonalC`), decode-extensional oracle,
  decode-extensional budget (`BudgetBy`), a physical cost model (`BudgetedSeparationOutput.WitnessCost` with `GeneralB`),
  and an explicit non-vacuity guard (`VacuityGuards`).
- This yields a direct internal separation between proof search and verification as algorithms,
  without asserting classical P != NP.

## P vs NP surfaces (four tiers)

The library intentionally provides four increasingly “classical” interfaces:

Conventions: route modules expose the quartet `Assumptions` / `Claim` / `Pack` / `mkPack`,
with `Pack.claim` as the canonical extractor.

1. **Grade-native kernel route (minimal separation pack):** `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda`
   - One-entry “spectral separation” pack used by the conditional P≠NP-shaped story.
   - Interface-first: bounds are *grades* on the kernel’s boundary flow (`Flow g (decode run)`), not raw time relations.
   - Kernel instantiations interpret grades via `ScaleOps` (budget + steps); classical alignment uses `gradeBound = τ`.
   - Generic names: `DetPolyTimeBoundedG` / `PolyWitnessedTotalVerificationG` (via `TruthRoute_Grade_Only.GradeBounded`).
   - Core implementation: `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda`.

2. **Witness-size refinement (within `TruthRoute`):**
   - `TruthRoute.For.WithWitnessSize` (adds explicit witness-size bounds to the verifier interface).

3. **Correctness-carrying interface (within `TruthRoute`):**
   - `TruthRoute.For.InP` and `TruthRoute.For.WithWitnessSize.InNP` (language-relative, correctness carried explicitly).

4. **Classical interface (literature-aligned, ℕ-bound):** `LogOS/Domain/Complexity/ClassicalPvsNP.agda`
   - Thin renaming of the grade-native physical classes specialized to ℕ-costs via `QNat` + `gradeBound = τ`.
   - `FromTruthRoute` reinterprets `TruthRoute.For.InP` / `TruthRoute.For.WithWitnessSize.InNP` as classical `InP` / `InNP` once you map
     `ComplexityModel.poly` into the shared polynomial predicate.

Canonical conditional route (kernel-native, minimal axioms):

- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (DetBottleneck + InfoHardness → PvsNPClaim)
- `Assumptions` is the explicit assumption pack (no circularity); `mkPack` produces the claim.
- This is the **default** high-assurance story: minimal assumptions, explicit dependencies.
  For ℕ polynomial predicates, use `PvsNPFromInfo_Grade_Only.FromNat` (via `PolyGrade.FromNat`).

The “strong-by-default” packaged claim object is:

- `LogOS/Domain/Complexity/PvsNP.agda` (packaging of `InNP` + `¬ InP`, no derivation)

Non-deterministic spine (shared with GRH/opacity):
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (proof-search oracle + budgeted opacity barrier)
  - General budgets: `ProofSearchOpacitySpine.For.Budgeted.GeneralB` (swap in any budget carrier).

Other routes:
- `TruthRoute_Grade_Only` (grade-only) is the canonical kernel-native story.
- `TruthRoute` (ℕ-bound via `gradeBound`) is a deprecated compatibility wrapper for literature-aligned interfaces.

## Quantitative bite: budgeted observability

The complexity story in LogOS is already resource-shaped (time/capacity/throughput).
The Opacity strand provides a complementary, *budgeted certificate* interface:

- `LogOS/Theorems/Meta/BudgetedTruthPositivity.agda` refines “observable” to
  “observable within budget `b`” (instantiate budgets as proof lengths, physical costs,
  or time-bounded Kt witnesses).
- `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda` proves a quantitative barrier:
  for each fixed budget, diagonalization forces an explicit input where any extensional
  budgeted observer must return `undefined`.

This is a direct formal hook for “poly-budget” claims: take the budget function to be
`p (size (decode γ))` (or any decode-extensional budget), and the same diagonal story
becomes a non-uniform lower bound statement about what can be fully certified under
that budget discipline.

## Where the code lives

- “Centerpiece” entrypoint (re-exports the story modules):
  - Implementation: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
  - Curated surface: `LogOS/Models/Complexity/Core.agda`
- Proof-search boundary (local checker → bounded search → unbounded search):
  - `LogOS/Domain/Complexity/ProofSearchBoundary.agda`
- Triple-axis resource schema (time + non-unitary events + classical info):
  - Grade-native core: `LogOS/Domain/Complexity/ResourceSchemaG.agda`,
    `LogOS/Domain/Complexity/ObservabilityBudgetG.agda`
  - GradeBound + ℕ-polynomial wrapper: `LogOS/Domain/Complexity/ResourceSchemaGraded.agda`,
    `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda`
  - LOB to info-bottleneck adapters: `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda`
    (grade-native) and `LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded.agda`
    (`FromLOBGradePG` grade-bound, `FromLOB` compat)
- Capstone theorem (generic “physics ⇒ no poly-budget decider”):
  - Grade-native core: `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`,
    `LogOS/Domain/Complexity/Targets/ProofSearchChainedTheoremGraded.agda`
  - DetWithin route (kernel-friendly abstraction): `ProofSearchCapstoneGraded.DetWithinRoute`
- Proof-search targets (verification vs search):
  - Grade-native core: `LogOS/Domain/Complexity/Targets/ProofSearchGraded.agda`,
    `LogOS/Domain/Complexity/Targets/ProofSearchQuantumPivotGraded.agda`
- TruthRoute bridge (connect to standard P/NP-style time/correctness notions):
  - `LogOS/Domain/Complexity/PhysToTruthRouteBridge.agda`
- Physical class interfaces + pipelines:
  - Grade-native core: `LogOS/Domain/Complexity/PhysicsClassesWGraded.agda`,
    `LogOS/Domain/Complexity/PhysProofBridgeWGraded.agda`,
    `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda`
  - Kernel route (TruthRoute-based): `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda` (module Kernel)
- SAT example target (nontrivial verifier cost, witness-size aligned):
  - `LogOS/Domain/Complexity/Targets/SATPhysicalSeparationCostGuardsGraded.agda` (kernel route in module Kernel)

## Examples

- Golden-path scaffold (grade-native → bridge → classical alignment): `LogOS/Domain/Complexity/Examples/GoldenPath.agda`
- Minsky scheme instantiation (machines-as-schemes factoring; Flow g = simulate (budget g)):
  `LogOS/Domain/Complexity/Examples/GoldenPathMinsky.agda` (includes `ScaleOps`-based budget hardening)

## Curated import (namespaced)

```text
open import LogOS.Models.Complexity.Core as Complexity
```

From that import, the stable surface exposes the proof-search boundary, the
resource schema, and the main capstone/bridge lemmas as a single navigable API.
For the P vs NP surface via the same import, use:

- `Complexity.PvsNP` (re-exported namespace)
- `Complexity.ClassicalPvsNP` (re-exported namespace)
- `Complexity.PvsNPFromInfo_Grade_Only` (minimal info-theory route)

Safe P/NP-only import (curated to avoid generic/compat surfaces):
`LogOS/Models/Complexity/PvsNP/Public.agda`.

## Audit build (one command)

```csh
agda --no-libraries -i . docs/DeepDive/Complexity.lagda.md
```
