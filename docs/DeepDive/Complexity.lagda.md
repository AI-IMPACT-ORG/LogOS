<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Complexity — LogOS (Verification vs Search)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.Complexity where

-- Sync guard: these imports anchor the pack surfaces this note describes.
-- If they drift, the docs build fails.
import LogOS.Packs.Complexity.Experimental.Core

```

This note is the single, publication-facing entrypoint for the **complexity**
architecture in the production library.

Interpretation (analogy):
the “physics” wording in this strand is a label for explicit cost/budget interfaces and hardness assumptions,
not a claim that LogOS derives physics from the kernel.

> **What this is / isn't**
> - **Not** a ZFC proof of classical P≠NP.
> - **Conditional:** if the stated assumptions hold in a model, the separation claim follows.
> - **Generic route:** the graded-flow interface (`DetPolyTimeBoundedG` / `PolyTotalWitnessedVerificationG`) is P/NP-shaped and total, not language-relative NP.
> - **Uniformity:** the canonical surface is fixed endomaps plus explicit encodings
>   (`TruthRoute_Grade_Only.Uniform`, `TruthRoute_Grade_Only.UniformNat`).
>   `UniformNatFromRuns` is a convenience adapter and is only uniform when the run
>   functions are fixed programs composed with the explicit encodings.
>   Non-uniform adapters are explicit (`TruthRoute_Grade_Only.NonUniform`).

The organizing principle is not “machines first”, but **interfaces first**:
LogOS makes the verification/search boundary explicit and then lets you choose
which computation surface instantiates it (UniversalIR, TMs, circuits, …).

## Terminology

- **P/NP-shaped** (grade-native): total verification interfaces such as
  `DetPolyTimeBoundedG` / `PolyTotalWitnessedVerificationG`; these are *not*
  language-relative NP.
- **Classical P/NP**: language-relative `InP` / `InNP` in
  `LogOS/Domain/Complexity/PvsNPLedger.agda`.

## Core idea: verification is local, search is global

LogOS internalises the split:

- **Verification**: given a candidate certificate/trace, checking is bounded.
- **Search / provability**: deciding existence of some certificate is an
  unbounded existential (a “global OR”), and that is where diagonal /
  observability bottlenecks appear.

This is packaged as the `ProofSearch`‑prefixed family under `LogOS/Domain/Complexity/*`
(with curated pack surfaces under `LogOS/Packs/Complexity/Experimental/*`).

## SAT as the front door (literature-aligned)

SAT is the canonical NP-complete target, so it is the front door for alignment:

- Definition + witness system: `LogOS/Domain/Complexity/Targets/SAT.agda`
- SAT ∈ NP (classical interface): `LogOS/Domain/Complexity/Targets/SAT.agda` (module `Classical`)
- ETH-aligned SAT pack (uniform, ℕ-bound): `LogOS/Domain/Complexity/Targets/SAT.agda` (module `ClassicalETH`)
- SAT NP-completeness axiom pack (reduction-based): `LogOS/Domain/Complexity/Targets/SAT.agda`
  (module `ClassicalNPComplete`, provides “SAT ∈ P ⇒ NP ⊆ P” via reduction transport).
  This is the standard Cook–Levin/Karp consequence; LogOS treats it as an explicit axiom pack.
  Under the physics-aligned hardness assumptions used elsewhere in this repo, the *ledger yields*
  a SAT∉P-shaped conclusion for the chosen encoding/budget notion, so the antecedent of this
  conditional is false in those models.
- SAT as proof search: `LogOS/Domain/Complexity/Targets/SATProofSearch.agda`
- Conditional separation pipeline (SAT + proof lower bound):
  `LogOS/Domain/Complexity/Targets/SAT.agda` (module `CostGuardsGraded`)
- SAT-from-physics assumption ledger:
  `LogOS/Domain/Complexity/Targets/SAT.agda` (module `CostGuardsGraded.For.SATFromProof`)

Cook–Levin and Karp NP-completeness are cited as external theorems and not re‑proved.

## Core ledger (opacity-aligned, proof-search first)

The strongest LogOS-native separation story is *proof-search opacity*:

- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (partial proof-search oracle + budgeted opacity barrier).
- Ledger-style assumptions mirror opacity/observability: diagonalization (`TruthDiagonalC`), decode-extensional (up to `_≈K_`) oracle,
  decode-extensional (up to `_≈K_`) budget (`BudgetBy`), a witness-cost model (`BudgetedSeparationOutput.WitnessCost`)
  (and optionally a general budget carrier via `SpectralSeparationOutput.GeneralB.WitnessCostB`),
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
   - Generic names: `DetPolyTimeBoundedG` / `PolyTotalWitnessedVerificationG`
     (via `TruthRoute_Grade_Only.Uniform.GradeBounded`).
   - Core implementation: `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda`.

2. **Witness-size refinement (uniform, ℕ-bound):**
   - `TruthRoute_Grade_Only.UniformNat.WithWitnessSize` (adds explicit witness-size bounds to the verifier interface).
   - Run-based uniform adapter: `TruthRoute_Grade_Only.UniformNatFromRuns.WithWitnessSize`.
   - Non-uniform adapter: `TruthRoute_Grade_Only.NonUniformNat.WithWitnessSize`.

3. **Correctness-carrying interface (uniform, ℕ-bound):**
   - `TruthRoute_Grade_Only.UniformNat.InP` and `TruthRoute_Grade_Only.UniformNat.WithWitnessSize.InNP`
     (language-relative, correctness carried explicitly).
   - Run-based uniform adapter: `TruthRoute_Grade_Only.UniformNatFromRuns.InP` and
     `TruthRoute_Grade_Only.UniformNatFromRuns.WithWitnessSize.InNP`.
   - Non-uniform adapter: `TruthRoute_Grade_Only.NonUniformNat.InP` and `TruthRoute_Grade_Only.NonUniformNat.WithWitnessSize.InNP`.

4. **Classical interface (literature-aligned, ℕ-bound):** `LogOS/Domain/Complexity/PvsNPLedger.agda`
   - Lightweight renaming of the grade-native physical classes specialized to ℕ-costs via `QNat` + `gradeBound = τ`.
   - `FromTruthRoute` reinterprets
     `TruthRoute_Grade_Only.UniformNatFromRuns.InP` / `TruthRoute_Grade_Only.UniformNatFromRuns.WithWitnessSize.InNP`
     as classical `InP` / `InNP` once you map
     `ComplexityModel.poly` into the shared polynomial predicate.

Canonical conditional route (kernel-native, minimal axioms):

- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (DetBottleneck + InfoHardness → PvsNPClaim)
- `Assumptions` is the explicit assumption pack (no circularity); `mkPack` produces the claim.
- This is the **default** high-assurance story: minimal assumptions, explicit dependencies.
  For ℕ polynomial predicates, use `PvsNPFromInfo_Grade_Only.FromNat` (via `PolyGrade.FromNat`).

Non-uniform adapter (explicit, opt-in):

- `TruthRoute_Grade_Only.NonUniform` (same semantics, but the encoding is explicit).

Non-deterministic spine (shared with opacity/observability):
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (proof-search oracle + budgeted opacity barrier)
  - General budgets: `ProofSearchOpacitySpine.For.Budgeted.General` (swap in any budget carrier).

Other routes:
- `TruthRoute_Grade_Only` is the canonical kernel-native story (grade-indexed bounds).
- ℕ-bounded convenience interfaces live in `TruthRoute_Grade_Only.UniformNat` (explicit `gradeBound : ℕ → grade`).
- ETH-shaped assumption (uniform, ℕ-bound): `TruthRoute_Grade_Only.UniformNat.ETHAssumption`.
- Proof-complexity lower bounds (verification vs search):
  `LogOS/Domain/Complexity/PhysProofBridgeWGraded.agda` (`ProofLowerBound`)
  + `LogOS/Domain/Complexity/Targets/ProofSearchGraded.agda`
  + `LogOS/Domain/Complexity/Targets/SATProofSearch.agda` (module `Graded`).
- Reductions and transport (many-one, poly-bounded): `LogOS/Domain/Complexity/Reduction.agda`
  (`Reduction.Classical.inPFromPolyReduction`, `Reduction.Classical.notInPFromPolyReduction`).

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
`p (size (decode γ))` (or any decode-extensional (up to `_≈K_`) budget), and the same diagonal story
becomes a non-uniform lower bound statement about what can be fully certified under
that budget discipline.

## Where the code lives

- “Centerpiece” entrypoint (re-exports the story modules):
  - Implementation: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
  - Curated surface (experimental): `LogOS/Packs/Complexity/Experimental/Core.agda`
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
  - `LogOS/Domain/Complexity/Targets/SAT.agda` (module `CostGuardsGraded.Kernel`)

## Barrier-aware framing (why this is conditional)

The pipeline is a conditional separation inside a model; it is not a ZFC proof of P≠NP.
The usual barrier results still apply to classical proofs:

- Relativization (Baker–Gill–Solovay, 1975)
- Natural proofs (Razborov–Rudich, 1997)
- Algebrization (2008)

## Examples

- Golden-path scaffold (grade-native → bridge → classical alignment): `LogOS/Domain/Complexity/Examples/GoldenPath.agda`
- Minsky scheme instantiation (machines-as-schemes factoring; Flow g = simulate (budget g)):
  `LogOS/Domain/Complexity/Examples/GoldenPath.agda` (module `Minsky`, includes `ScaleOps`-based budget hardening)

## Curated import (namespaced)

```text
open import LogOS.Packs.Complexity.Experimental.Surface as Complexity
```

From that import, the experimental surface exposes the proof-search boundary,
the resource schema, and the main capstone/bridge lemmas as a single navigable API.
For the P vs NP surfaces via the same import, use:

- `Complexity.PvsNP.PvsNP_Grade_Only` (grade-native kernel route)
- `Complexity.PvsNP.PvsNPLedger` (literature-aligned surface)
- `Complexity.PvsNP.PvsNPFromInfo_Grade_Only` (minimal info-theory route)

Safe P/NP-only import (curated to avoid generic/compat surfaces):
`LogOS/Packs/Complexity/Experimental/PvsNP/Public.agda`.

## Bibliography pointers (not exhaustive)

- S. A. Cook (1971), "The Complexity of Theorem-Proving Procedures".
- R. M. Karp (1972), "Reducibility Among Combinatorial Problems".
- S. A. Cook and R. A. Reckhow (1979), "The Relative Efficiency of Propositional Proof Systems".
- M. Blum (1967), "A Machine-Independent Theory of the Complexity of Recursive Functions".
- S. Arora and B. Barak (2009), "Computational Complexity: A Modern Approach".
- S. Aaronson (2005), "NP-complete Problems and Physical Reality".
- T. Baker, J. Gill, R. Solovay (1975), "Relativizations of the P = ? N P Question".
- A. Razborov, S. Rudich (1997), "Natural Proofs".
- S. Aaronson, A. Wigderson (2008), "Algebrization: A New Barrier in Complexity Theory".

## Audit build (one command)

```csh
agda --no-libraries -i . docs/DeepDive/Complexity.lagda.md
```
