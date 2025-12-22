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

## Assumption ledger (one screen)

| Claim | Depends on | Type strength | Where used |
|---|---|---|---|
| `PhysSeparationPipelineWCostGuardsGraded.Claim L` | `PhysNPwCostGuards` witness system, `MergeMeasure`, `ProofLowerBound` | Conditional lower-bound schema (physics/model-supplied) | Grade-native core: `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda` (`Assumptions`, `mkPack`); kernel route: `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda` (module Kernel) |
| `PvsNP.Claim L` | `InNP L` + `¬ InP L` | Language-relative + correctness (`InNP` / `¬ InP`) | `LogOS/Domain/Complexity/PvsNP.agda` (`mkPack`) |
| `PvsNPPackG` | `PolyWitnessedTotalVerificationG` + `SuperPolyHardnessG` | P/NP-shaped graded-flow interface (not language-relative) | `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda` (`mkPvsNPG`) |
| `SuperPolyHardnessG` | `DetBottleneck` + `InfoHardness` | Minimal info-theory route | `LogOS/Domain/Complexity/InfoHardnessBridge.agda` (`detSuperPolyFromInfo`) |
| `PvsNPClaimG` (info route) | `Assumptions` (NP witness + bottleneck + hardness) | Minimal conditional pack (no circularity) | `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (`Assumptions`, `mkPack`) |

## Pipeline sketch (generic → TruthRoute → physical)

```mermaid
flowchart TD
  A[Generic graded-flow interface<br/>DetPolyTimeBoundedG / PolyWitnessedTotalVerificationG]
  B[P/NP-shaped claim pack<br/>PvsNPPackG]
  C[Physical assumptions<br/>MergeMeasure + ProofLowerBound + PhysNPwCostGuards]
  D[PhysNPwCostGuards != PhysPCostGuards]
  E[Bridge (grade reindexing)]
  F[PvsNP.Claim<br/>InNP / not InP]

  A --> B
  C --> D --> E --> F
  B --> D
```

Canonical high-assurance story: the info‑hardness route (`DetBottleneck` + `InfoHardness`)
is the default; the merge‑count physical route is optional and clearly labeled as such.

## Minimal physical axioms (info-theory aligned)

The LogOS-native minimal assumption is the *DetBottleneck* interface:
any run within a bound `t` cannot exceed a budgeted amount of classical
information (with a single constant `κ`).

- Interface: `LogOS/Domain/Complexity/InfoHardnessBridge.agda` (`DetBottleneck`, `InfoHardness`)
- Physically aligned split axioms (density/volume reading):
  `MinInfoDensity` + `SuperPolyResolution`, with
  `infoHardnessFromDensityAxioms` in the same module.
- Canonical LOB adapter (grade-native): `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda` (`FromLOB`)
- Compatibility adapter (graded, ℕ-bound): `LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded.agda` (`FromLOB`)

LOB is a standard source of such a bottleneck (grade-native `LOB` or compat `LOBG`),
but it is not the only one.
Any axiom pack that yields a `DetBottleneck` can plug into the same pipeline.

No circularity: `InfoHardness` is an *input* axiom. `SuperPolyHardness` and the
P≠NP‑shaped claims are derived from it, not assumed.

Grade-native assumption packs are available via `PvsNPFromInfo_Grade_Only.For.WithAcc.Assumptions`
(using `PolyGrade` / `PolyPredG`) and the graded interface under `PvsNPFromInfo_Grade_Only.For.G`.
To reuse an ℕ polynomial predicate, use `PvsNPFromInfo_Grade_Only.FromNat` (via `PolyGrade.FromNat`).

Non-degeneracy / I/O realism (explicit guardrails):
- `LogOS/Domain/Complexity/StandardCMLaws.agda` (`EncodingsInDomain`, `ReasonableSize`)
- `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda` (`NonDegenerate`: size-to-grade budget covers input)
- `LogOS/Domain/Complexity/Examples/GoldenPathMinsky.agda` (`SizeBudget`, `cost≤budget` via `ScaleOps`)
Core operationalization of grades: `LogOS/Minimal/ScaleOps.agda` (Scale → Time → steps).

## End-to-end alignment to standard P/NP

The most LogOS-aligned chain goes straight through the kernel:

1. Kernel-native bounds: `TruthRoute_Grade_Only` (graded Flow on decoded runs).
2. Minimal physics: `DetBottleneck` + `InfoHardness`.
3. Conditional separation: `PvsNPFromInfo_Grade_Only` (builds `PvsNPPackG` / `PvsNPClaimG`).
4. Language-relative claims: `PvsNP`.
5. Literature alignment: `ClassicalPvsNP.FromTruthRoute`.

See also the tiny end-to-end skeleton in:

- `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda`
- `LogOS/Domain/Complexity/Examples/InfoRouteChainIR.agda` (example UniversalIR instantiation shell)
- `LogOS/Domain/Complexity/Examples/GoldenPath.agda` (grade-native → bridge → classical alignment)
- `LogOS/Domain/Complexity/Examples/GoldenPathMinsky.agda` (concrete Minsky scheme instantiation)

Concrete Minsky route (kernel closed, decode = id; Flow g = simulate (budget g)):

```agda
module _ (Pℕ : LogOS.Domain.Complexity.Poly.PolyPred) where
  open LogOS.Domain.Complexity.Examples.GoldenPathMinsky.Concrete Pℕ public
```

Witness sizes for UniversalIR are now nontrivial: `LogOS/Domain/UniversalIR/Size.agda`
defines `ucodeSize`, and `UniversalIRCM` uses it as `wsize`.

## The compositional bridge: an explicit information bottleneck interface

To maximize payoff without touching the Kernel, the library factors the
“Det-superpoly” assumption into an information-theoretic interface that composes
with existing throughput/capacity packs:

- Info hardness ⇒ superpoly hardness bridge:
  - `LogOS/Domain/Complexity/InfoHardnessBridge.agda`
- Wrapper: derive the existing PvsNP claim from NP witness + info bottleneck:
- `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (grade-native)
- Concrete adapters from measurement/capacity packs:
  - `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda` (grade-native)
  - `LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded.agda` (`FromLOBGradePG`, `FromLOBGradeG`, `FromLOB`)

## Physical axiom packs (where locality/causality/unitarity live)

The physics vocabulary is kept as small, opt‑in packs under `LogOS/Domain/Universality/*`,
so the “physics ⇒ separation” theorem remains auditable:

- Locality/causality/local unitarity → Landauer-style bottleneck:
  - `LogOS/Domain/Universality/LCUToLandauer.agda`
- Measurement / non-unitary capacity pivots:
  - `LogOS/Domain/Universality/MeasurementCapacity.agda`
  - `LogOS/Domain/Universality/NonUnitaryCapacity.agda`
  - `LogOS/Domain/Universality/InfoProcessingBounds.agda`

## Universal computation surface

To avoid baking in one machine model, the intended computation substrate is the
UniversalIR “one process, many paradigms” surface:

- UniversalIR core: `LogOS/Domain/UniversalIR/` (Minsky, Lambda, Ethereum, Quantum, Circuit)
- Schemes interface: `LogOS/Domain/UniversalIR/Schemes.agda`
- Namespaced wrapper: `LogOS/Models/UniversalIR/Core.agda`

## Targets (SAT)

- SAT physical separation (nontrivial check-cost, witness-size aligned):
  - Grade-native core: `LogOS/Domain/Complexity/Targets/SATPhysicalSeparationCostGuardsGraded.agda`
  - Kernel route: `LogOS/Domain/Complexity/Targets/SATPhysicalSeparationCostGuardsGraded.agda` (module Kernel)
- SAT as proof search (proofs = assignments): `LogOS/Domain/Complexity/Targets/SATProofSearch.agda`

## Audit build (one command)

```csh
agda --no-libraries -i . docs/Application_PvsNP.lagda.md
```
