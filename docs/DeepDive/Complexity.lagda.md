<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Complexity — LogOS (Verification vs Search)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.Complexity where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.Complexity.Surface
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

This is packaged as the `ProofSearch`‑prefixed family under `LogOS/Domain/Complexity/*`
(with curated pack surfaces under `LogOS/Packs/Complexity/*`).

## Core ledger (opacity-aligned, proof-search first)

The strongest LogOS-native separation story is *proof-search opacity*:

- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (partial proof-search oracle + budgeted opacity barrier).
- Ledger-style assumptions mirror opacity/observability: diagonalization (`TruthDiagonalC`), decode-extensional oracle,
  decode-extensional budget (`BudgetBy`), a witness-cost model (`BudgetedSeparationOutput.WitnessCost`)
  (and optionally a general budget carrier via `BudgetedSeparationOutput.GeneralB.WitnessCostB`),
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

2. **Witness-size refinement (within `TruthRoute_Grade_Only.ForNat`):**
   - `TruthRoute_Grade_Only.ForNat.WithWitnessSize` (adds explicit witness-size bounds to the verifier interface).

3. **Correctness-carrying interface (within `TruthRoute_Grade_Only.ForNat`):**
   - `TruthRoute_Grade_Only.ForNat.InP` and `TruthRoute_Grade_Only.ForNat.WithWitnessSize.InNP`
     (language-relative, correctness carried explicitly).

4. **Classical interface (literature-aligned, ℕ-bound):** `LogOS/Domain/Complexity/ClassicalPvsNP.agda`
   - Thin renaming of the grade-native physical classes specialized to ℕ-costs via `QNat` + `gradeBound = τ`.
   - `FromTruthRoute` reinterprets
     `TruthRoute_Grade_Only.ForNat.InP` / `TruthRoute_Grade_Only.ForNat.WithWitnessSize.InNP`
     as classical `InP` / `InNP` once you map
     `ComplexityModel.poly` into the shared polynomial predicate.

Canonical conditional route (kernel-native, minimal axioms):

- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (DetBottleneck + InfoHardness → PvsNPClaim)
- `Assumptions` is the explicit assumption pack (no circularity); `mkPack` produces the claim.
- This is the **default** high-assurance story: minimal assumptions, explicit dependencies.
  For ℕ polynomial predicates, use `PvsNPFromInfo_Grade_Only.FromNat` (via `PolyGrade.FromNat`).

Legacy wrapper (packaging-only, not part of the curated surface):

- `LogOS/Domain/Complexity/Legacy/PvsNP.agda` (repackages `InNP` + `¬ InP`, no derivation)

Non-deterministic spine (shared with opacity/observability):
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (proof-search oracle + budgeted opacity barrier)
  - General budgets: `ProofSearchOpacitySpine.For.Budgeted.GeneralB` (swap in any budget carrier).

Other routes:
- `TruthRoute_Grade_Only` is the canonical kernel-native story (grade-indexed bounds).
- ℕ-bounded convenience interfaces live in `TruthRoute_Grade_Only.ForNat` (explicit `gradeBound : ℕ → grade`).

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
  - Curated surface: `LogOS/Packs/Complexity/Core.agda`
- Proof-search boundary (local checker → bounded search → unbounded search):
  - `LogOS/Domain/Complexity/ProofSearchBoundary.agda`
- Triple-axis resource schema (time + non-unitary events + classical info):
  - Grade-native core: `LogOS/Domain/Complexity/ResourceSchemaG.agda`,
    `LogOS/Domain/Complexity/ObservabilityBudgetG.agda`
  - GradeBound + ℕ-polynomial wrapper: `LogOS/Domain/Complexity/ResourceSchemaGraded.agda`,
    `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda`
  - LOB to info-bottleneck adapters: `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda` (grade-native `FromLOB`)
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
open import LogOS.Packs.Complexity.Surface as Complexity
```

From that import, the stable surface exposes the proof-search boundary, the
resource schema, and the main capstone/bridge lemmas as a single navigable API.
For the P vs NP surfaces via the same import, use:

- `Complexity.PvsNP_Grade_Only` (grade-native kernel route)
- `Complexity.ClassicalPvsNP` (literature-aligned surface)
- `Complexity.PvsNPFromInfo_Grade_Only` (minimal info-theory route)

Safe P/NP-only import (curated to avoid generic/compat surfaces):
`LogOS/Packs/Complexity/PvsNP/Public.agda`.

## Audit build (one command)

```csh
agda --no-libraries -i . docs/DeepDive/Complexity.lagda.md
```
