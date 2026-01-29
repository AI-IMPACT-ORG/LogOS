<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Complexity via Physical Bottlenecks — LogOS (Conditional)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.Complexity where

-- Sync guard: these imports anchor the pack surfaces referenced below.
-- If they drift, the docs build fails.
import LogOS.Packs.Complexity.Experimental.Core
import LogOS.Packs.Complexity.Experimental.PvsNP.Public
import LogOS.Packs.Complexity.Experimental.Applications.All

-- Identifier sync guards (claim-heavy): these names are referenced in the prose.
import LogOS.Domain.Complexity.PvsNPLedger as PvsNP
import LogOS.Domain.Complexity.ProofSearchOpacitySpine as PSOS
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TR
open import LogOS.Theorems.Meta.BudgetedSeparationOutput using (WitnessCost)

module PvsNPFor = PvsNP.For
module PvsNPFromTruthRoute = PvsNP.FromTruthRoute
module PSOSFor = PSOS.For
module TRUniformNatFromRuns = TR.UniformNatFromRuns

```

Trust level: **experimental**. This pack is under evaluation and should be
considered less stable than the rest of the repository. It is a conditional,
model-driven complexity story; do not read it as a ZFC proof claim.

Interpretation (analogy):
the “physics” wording in this note is a label for explicit resource/cost assumption records.
No physical semantics is imported by default; only the cited Agda assumptions and theorems apply.

> **What this is / isn't**
> - **Not** a ZFC proof of classical complexity separation.
> - **Conditional:** if the stated physical/verification assumptions hold in a model, the separation claim follows.
> - **Generic route:** the graded-flow interface (`DetPolyTimeBoundedG` / `PolyTotalWitnessedVerificationG`) is P/NP-shaped and total, not language-relative NP.
> - **Uniformity:** the canonical surface is `TruthRoute_Grade_Only.Uniform` / `UniformNat`
>   (explicit encodings + fixed endomaps). `UniformNatFromRuns` is a convenience adapter and
>   is only uniform when the run functions are fixed programs composed with the explicit
>   encodings. Non-uniform adapters are explicit.
> **Reviewer quick-check**
> - **Where does hardness come from?** It is an explicit axiom (`InfoHardness` or `ProofLowerBound`), not derived.
> - **Is this classical P≠NP?** No; classical alignment is via
>   `TruthRoute_Grade_Only.UniformNatFromRuns` + `PvsNPLedger` (non-uniform variants are explicit).
> - **What is the minimal meaningful target?** SAT + non-degeneracy laws.

**Terminology note**
- “P/NP-shaped” here refers to total verification interfaces (`PolyTotalWitnessedVerificationG`),
  not language-relative NP. Classical NP is only via `PvsNPLedger`.

This note is the single, publication-facing entrypoint for the “complexity from
physics” story in the production library.

Safe import (curated experimental complexity surfaces only): `LogOS/Packs/Complexity/Experimental/PvsNP/Public.agda`.

## SAT as the canonical target

- Definition + witness system: `LogOS/Domain/Complexity/Targets/SAT.agda`
- SAT as proof search: `LogOS/Domain/Complexity/Targets/SATProofSearch.agda` (module `Graded`)
- Conditional separation pipeline (SAT + proof lower bound):
  `LogOS/Domain/Complexity/Targets/SAT.agda` (module `CostGuardsGraded`)
- NP-completeness axiom pack (reduction-based): `LogOS/Domain/Complexity/Targets/SAT.agda`
  (module `ClassicalNPComplete`, provides “SAT ∈ P ⇒ NP ⊆ P” via reduction transport)
  This is the standard Cook–Levin/Karp argument, stated as an explicit axiom pack.
  Under the physics-aligned hardness assumptions in this pack, the *ledger yields*
  a SAT∉P-shaped conclusion for the chosen encoding/budget notion, so the antecedent
  does not hold in those models.
- SAT-from-physics assumption ledger:
  `LogOS/Domain/Complexity/Targets/SAT.agda` (module `CostGuardsGraded.For.SATFromProof`)

The claim is deliberately **conditional**: LogOS does not assert a proof of
classical separation in ZFC. What it *does* provide is a clean pipeline:

> physically aligned bottleneck axioms + universal computation surface  
> ⇒ a sufficient condition for a separation claim

Proof-search opacity spine (opacity core, reused here):
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda`
- This re-exports the spectral/budgeted separation machinery and applies it to
  proof-search oracles, keeping the hardness story non-deterministic.
- Budgets are first-class: use `ProofSearchOpacitySpine.For.Budgeted.General` to
  swap in any budget carrier (ℕ, quantale scales, physical cost models).

Many-one reductions (literature-aligned baseline):
- `LogOS/Domain/Complexity/Reduction.agda` (many-one + poly-bounded reductions, decider transport).
  Use `Reduction.Classical.inPFromPolyReduction` and
  `Reduction.Classical.notInPFromPolyReduction` for transport along reductions.

## Two layers: “proof-search separation” and “classical-looking complexity”

1) **Foundational layer (centerpiece):** verification vs unbounded search under
budgeted classicalization.

- Narrative/theorem surface: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
- Capstone theorem (grade-native core): `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`

2) **Bridge layer:** connect physical “no poly-budget decider” conclusions back
to standard P/NP-style time/correctness predicates.

- Bridge (grade reindexing): `LogOS/Domain/Complexity/PhysToTruthRouteBridge.agda`

For a literature-aligned classical interface (ℕ-bound compat; cost = time), use:

- `LogOS/Domain/Complexity/PvsNPLedger.agda` (namespaced as `LogOS.Packs.Complexity.Experimental.Core.PvsNPLedger`)

For the minimal info-theory route (kernel-native, conditional), use:

- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (namespaced as `LogOS.Packs.Complexity.Experimental.Core.PvsNPFromInfo_Grade_Only`)

## The strongest explicit axiom ledger (opacity-aligned style)

You can package the PvsNP-style claim without assuming P != NP by making the
following explicit assumptions in a record (ledger):

1) Diagonalization (metalogical, opacity-style)
   - `TruthDiagonalC Code (ProofSearchOpacitySpine.For.Budgeted.WithinBudgetBy ...)`
   - This is the same metalogical assumption used in opacity; it is explicit.
2) Proof-search oracle (partial, decode-extensional up to `_≈K_`)
   - `ProofSearchOpacitySpine.For.ProofSearchOracle`
   - This does not assume totality.
3) Budget function is decode-extensional up to `_≈K_`
   - `ProofSearchOpacitySpine.For.BudgetBy` (budget + extensionality)
   - Keeps budget discipline aligned with the kernel's decoded mutual refinement (`_≈K_`).
4) Witness cost / physical budget
   - ℕ-cost surface: `BudgetedSeparationOutput.WitnessCost`
   - General budgets: `SpectralSeparationOutput.GeneralB.WitnessCostB`
   - This is where "physics-aligned" lives: choose cost = info/energy/irreversible events.
5) Non-vacuity guard (no "all undefined" oracle)
   - `ProofSearchOpacitySpine.For.VacuityGuards` (some code is within budget)
6) Verification is poly-bounded
   - If you want "verification in P", add a polynomial check bound (e.g. via
     `ProofSearchGraded` or `LanguageWitnessW`), and the standard non-degeneracy
     guardrails from `LogOS/Domain/Complexity/Model.agda` (module `StandardCMLaws`).
7) Classical alignment (literature-aligned)
   - Use `LogOS/Domain/Complexity/PvsNPLedger.agda` with `QNat` and `gradeBound = τ`
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

- `LogOS/Domain/Complexity/Model.agda` (`StandardCMLaws.EncodingsInDomain`, `StandardCMLaws.ReasonableSize`)
- `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda` (`NonDegenerate`)
- `LogOS/Domain/Complexity/Examples/GoldenPath.agda` (`Minsky.For.SizeBudget`, `Minsky.For.cost≤budget`)
- `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` (`VacuityGuards`)
- `LogOS/Domain/Complexity/MeasurementCapacity.agda` (`MeasurementCapacityGuards`, `NonUnitaryCapacityGuards`)
- `LogOS/Domain/Complexity/SecondLaw.agda` (`SecondLawGuards`)

These keep the ledger honest by ruling out degenerate encodings and vacuous
resource bounds.

## Optional routes and instantiations (tucked away)

- Info‑hardness route (DetBottleneck + InfoHardness):
  `LogOS/Domain/Complexity/InfoHardnessBridge.agda`,
  `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda`
- ETH-shaped assumption (uniform, ℕ-bound):
  `TruthRoute_Grade_Only.UniformNat.ETHAssumption` and
  `LogOS/Domain/Complexity/Targets/SAT.agda` (module `ClassicalETH`)
- Proof-complexity lower bounds (verification vs search):
  `LogOS/Domain/Complexity/PhysProofBridgeWGraded.agda` (`ProofLowerBound`)
  + `LogOS/Domain/Complexity/Targets/SATProofSearch.agda`
- Physical axiom packs:
  `LogOS/Domain/Complexity/LCUToLandauer.agda`,
  `LogOS/Domain/Complexity/MeasurementCapacity.agda`
  (records `MeasurementCapacity`, `NonUnitaryCapacity` with optional non-vacuity guards),
  `LogOS/Domain/Complexity/SecondLaw.agda` (record `SecondLawAssumptions` with `SecondLawGuards`),
  `LogOS/Domain/Complexity/InfoProcessingBounds.agda`
- Classical alignment pipeline:
  `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda` (module `UniformNatFromRuns`) →
  `LogOS/Domain/Complexity/PvsNPLedger.agda`
  (uniform encodings live in `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda`
  (module `UniformNat`; non-uniform adapter: `NonUniformNat`))
- UniversalIR substrate and examples:
  `LogOS/Domain/UniversalIR/`,
  `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda`,
  `LogOS/Domain/Complexity/Examples/GoldenPath.agda`
- Target example (SAT):
  `LogOS/Domain/Complexity/Targets/SAT.agda`
  - Kernel route: `LogOS/Domain/Complexity/Targets/SAT.agda` (module `CostGuardsGraded.Kernel`)
- SAT as proof search (proofs = assignments): `LogOS/Domain/Complexity/Targets/SATProofSearch.agda`

## Barrier-aware framing

This is a conditional separation inside a model, not a ZFC proof of P≠NP.
Classical barrier results still apply to ZFC proofs:

- Relativization (Baker–Gill–Solovay, 1975)
- Natural proofs (Razborov–Rudich, 1997)
- Algebrization (2008)

## Bibliography pointers (not exhaustive)

- S. A. Cook (1971), "The Complexity of Theorem-Proving Procedures".
- R. M. Karp (1972), "Reducibility Among Combinatorial Problems".
- S. A. Cook and R. A. Reckhow (1979), "The Relative Efficiency of Propositional Proof Systems".
- M. Blum (1967), "A Machine-Independent Theory of the Complexity of Recursive Functions".
- R. Landauer (1961), "Irreversibility and Heat Generation in the Computing Process".
- C. H. Bennett (1982), "The Thermodynamics of Computation - A Review".
- S. Arora and B. Barak (2009), "Computational Complexity: A Modern Approach".
- S. Aaronson (2005), "NP-complete Problems and Physical Reality".
- T. Baker, J. Gill, R. Solovay (1975), "Relativizations of the P = ? N P Question".
- A. Razborov, S. Rudich (1997), "Natural Proofs".
- S. Aaronson, A. Wigderson (2008), "Algebrization: A New Barrier in Complexity Theory".

## Audit build (one command)

```csh
agda --no-libraries -i . docs/Applications/Complexity.lagda.md
```
