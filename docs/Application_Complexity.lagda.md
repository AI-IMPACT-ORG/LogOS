<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Complexity via Physical Bottlenecks — LogOS (Conditional)

```agda
{-# OPTIONS --safe #-}
module docs.Application_Complexity where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.Complexity.Surface
```

> **What this is / isn't**
> - **Not** a ZFC proof of classical complexity separation.
> - **Conditional:** if the stated physical/verification assumptions hold in a model, the separation claim follows.
> - **Generic route:** the graded-flow interface (`DetPolyTimeBoundedG` / `PolyWitnessedTotalVerificationG`) is P/NP-shaped, not language-relative NP.
> **Reviewer quick-check**
> - **Where does hardness come from?** It is an explicit axiom (`InfoHardness` or `ProofLowerBound`), not derived.
> - **Is this classical P≠NP?** No; classical alignment is only via `TruthRoute_Grade_Only.ForNat` + `ClassicalPvsNP`.
> - **What is the minimal meaningful target?** SAT + non-degeneracy laws.

This note is the single, publication-facing entrypoint for the “complexity from
physics” story in the production library.

Safe import (curated complexity surfaces only): `LogOS/Packs/Complexity/PvsNP/Public.agda`.

The claim is deliberately **conditional**: LogOS does not assert a proof of
classical separation in ZFC. What it *does* provide is a clean pipeline:

> physically aligned bottleneck axioms + universal computation surface  
> ⇒ a sufficient condition for a separation claim

The legacy PvsNP language-relative pack is a **wrapper**: its `Assumptions` already
contain `InNP L` and `¬ InP L`, and `mkPack` only rewraps that data.

Proof-search opacity spine (opacity core, reused here):
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda`
- This re-exports the spectral/budgeted separation machinery and applies it to
  proof-search oracles, keeping the hardness story non-deterministic.
- Budgets are first-class: use `ProofSearchOpacitySpine.For.Budgeted.GeneralB` to
  swap in any budget carrier (ℕ, quantale scales, physical cost models).

## Two layers: “proof-search separation” and “classical-looking complexity”

1) **Foundational layer (centerpiece):** verification vs unbounded search under
budgeted classicalization.

- Narrative/theorem surface: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
- Capstone theorem (grade-native core): `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`

2) **Bridge layer:** connect physical “no poly-budget decider” conclusions back
to standard P/NP-style time/correctness predicates.

- Bridge (grade reindexing): `LogOS/Domain/Complexity/PhysToTruthRouteBridge.agda`

Legacy wrapper (packaging-only, not part of the curated surface):

- `LogOS/Domain/Complexity/Legacy/PvsNP.agda` (repackages `InNP` + `¬ InP`, no derivation)

For a literature-aligned classical interface (ℕ-bound compat; cost = time), use:

- `LogOS/Domain/Complexity/ClassicalPvsNP.agda` (namespaced as `LogOS.Packs.Complexity.Core.ClassicalPvsNP`)

For the minimal info-theory route (kernel-native, conditional), use:

- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (namespaced as `LogOS.Packs.Complexity.Core.PvsNPFromInfo_Grade_Only`)

## The strongest explicit axiom ledger (opacity-aligned style)

You can package the PvsNP-style claim without assuming P != NP by making the
following explicit assumptions in a record (ledger):

1) Diagonalization (metalogical, opacity-style)
   - `TruthDiagonalC Code (WithinBudgetBy ...)`
   - This is the same metalogical assumption used in opacity; it is explicit.
2) Proof-search oracle (partial, decode-extensional)
   - `ProofSearchOpacitySpine.For.ProofSearchOracle`
   - This does not assume totality.
3) Budget function is decode-extensional
   - `ProofSearchOpacitySpine.For.BudgetBy` (budget + extensionality)
   - Keeps budget discipline aligned with the kernel's decode-equality.
4) Witness cost / physical budget
   - ℕ-cost surface: `BudgetedSeparationOutput.WitnessCost`
   - General budgets: `BudgetedSeparationOutput.GeneralB.WitnessCostB`
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

## Relation to literature

This application is designed to recover and generalize several familiar
complexity strands, while keeping assumptions explicit:

- **Proof complexity / search vs verification:** the proof-search separation
  surface mirrors the Cook-Reckhow style split between searching for proofs and
  verifying them, but is parameterized by an explicit budget carrier.
- **Physical complexity bounds:** the Info/Landauer/measurement-capacity packs
  align with information-theoretic lower bounds on computation, now stated as
  reusable assumption records rather than implicit claims.
- **Conditional separations:** the P-vs-NP shaped claims are explicitly
  conditional on hardness/diagonalization ledgers; the generalization is that
  the same pipeline works for any budget notion (time, energy, information).

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
  `LogOS/Domain/Complexity/LCUToLandauer.agda`,
  `LogOS/Domain/Complexity/MeasurementCapacity.agda`,
  `LogOS/Domain/Complexity/NonUnitaryCapacity.agda`,
  `LogOS/Domain/Complexity/InfoProcessingBounds.agda`
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

## Bibliography pointers (not exhaustive)

- S. A. Cook (1971), "The Complexity of Theorem-Proving Procedures".
- R. M. Karp (1972), "Reducibility Among Combinatorial Problems".
- S. A. Cook and R. A. Reckhow (1979), "The Relative Efficiency of Propositional Proof Systems".
- M. Blum (1967), "A Machine-Independent Theory of the Complexity of Recursive Functions".
- R. Landauer (1961), "Irreversibility and Heat Generation in the Computing Process".
- C. H. Bennett (1982), "The Thermodynamics of Computation - A Review".
- S. Arora and B. Barak (2009), "Computational Complexity: A Modern Approach".

## Audit build (one command)

```csh
agda --no-libraries -i . docs/Application_Complexity.lagda.md
```
