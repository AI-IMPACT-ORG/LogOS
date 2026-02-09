<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Complexity Layout
=================

Interpretation (analogy):
this directory sometimes uses “physics of information” vocabulary (e.g. Landauer/RG) as motivation; the formal content is only what is stated in the referenced Agda modules.

Publication-facing entrypoint
-----------------------------

- Narrative spine: `docs/DeepDive/Complexity.lagda.md`
- Namespaced wrapper (experimental surface): `LogOS/Packs/Complexity/Experimental/Core.agda`

Main modules (this directory)
-----------------------------

- Narrative-first aggregator: `LogOS/Complexity/ProofSearchSeparation.agda`
- Minimal proof-system interface: `LogOS/Syntax/ProofSystem.agda`
- Proof-search boundary (verification vs bounded search vs unbounded search): `LogOS/Complexity/ProofSearchBoundary.agda`
- Proof-search opacity spine (shared with GRH/opacity machinery): `LogOS/Complexity/ProofSearchOpacitySpine.agda`
  (general budgets via `ProofSearchOpacitySpine.For.Budgeted.General`;
   decode-ext budgets via `ProofSearchOpacitySpine.For.BudgetBy`;
   non-vacuity guard via `ProofSearchOpacitySpine.For.VacuityGuards`)
- Capstone (grade-native): `LogOS/Complexity/ProofSearchCapstoneGraded.agda`
- One-entry theorem (grade-native): `LogOS/Complexity/Targets/ProofSearchChainedTheoremGraded.agda`
- DetWithin route (kernel-friendly abstraction): `ProofSearchCapstoneGraded.DetWithinRoute`

Pack conventions
----------------

- Most routes expose a standard quartet: `Assumptions`, `Claim`, `Pack`, `mkPack`.
- `Pack.claim` is the canonical way to extract the claim from assumptions.

P/NP interfaces and bridges
---------------------------

These modules do **not** provide a ZFC proof of classical `P ≠ NP`. All separation
claims are explicitly conditional on the stated assumptions in each pack.

- Recommended experimental surface: `LogOS/Packs/Complexity/Experimental/Core.agda`
- Safe P/NP-only surface: `LogOS/Packs/Complexity/Experimental/PvsNP/Public.agda`
- Meta note: `LogOS/Theorems/Meta/SpectralSeparationOutput.agda`

- Conditional P/NP-shaped pack (grade-native interface): `LogOS/Complexity/PvsNP_Grade_Only.agda`
- Canonical minimal route (info-theory): `LogOS/Complexity/PvsNPFromInfo_Grade_Only.agda`
  (`Assumptions`, `mkPack`)
- ℕ polynomial predicates can be lifted via `PvsNPFromInfo_Grade_Only.FromNat` (`PolyGrade.FromNat`).
- Classical P/NP interface (literature-aligned, ℕ-bound): `LogOS/Complexity/PvsNPLedger.agda`
- Reduction transport (many-one, poly-bounded): `LogOS/Complexity/Reduction.agda`
  (`Reduction.Classical.inPFromPolyReduction`, `Reduction.Classical.notInPFromPolyReduction`)
- Truth-route family: `LogOS/Complexity/TruthRoute_Grade_Only.agda` (grade-only, canonical).
  Uniform route: `TruthRoute_Grade_Only.Uniform`, `TruthRoute_Grade_Only.UniformNat`,
  and run-based `TruthRoute_Grade_Only.UniformNatFromRuns`;
  non-uniform adapters live in `TruthRoute_Grade_Only.NonUniform` / `TruthRoute_Grade_Only.NonUniformNat`.
- ETH-shaped assumption (uniform, ℕ-bound): `TruthRoute_Grade_Only.UniformNat.ETHAssumption`
  (SAT pack: `LogOS/Complexity/Targets/SAT.agda` module `ClassicalETH`).
- Optional non-degeneracy laws: `LogOS/Complexity/Model.agda` (module `StandardCMLaws`)

Information/physics routes
--------------------------

- Physics-of-information axiom packs:
  `LogOS/Complexity/LCUToLandauer.agda`,
  `LogOS/Complexity/SecondLaw.agda`,
  `LogOS/Complexity/MeasurementCapacity.agda` (record `NonUnitaryCapacity`),
  `LogOS/Complexity/DataProcessingInequality.agda`,
  `LogOS/Complexity/InfoProcessingBounds.agda`
  (curated surface: `LogOS/Packs/Complexity/Experimental/PhysicsOfInformation.agda`)

- Polynomial predicate + arithmetic helpers:
  `LogOS/Complexity/Poly.agda`, `LogOS/Complexity/PolyGrade.agda`,
  `LogOS/Complexity/Arithmetic.agda`
- Info-hardness bridge (info-theory route):
  `LogOS/Complexity/InfoHardnessBridge.agda`
- Convenience pack: `LogOS/Complexity/PvsNPFromInfo_Grade_Only.agda`
- Grade-native resource schema and LOB packs:
  `LogOS/Complexity/ResourceSchemaG.agda`, `LogOS/Complexity/ObservabilityBudgetG.agda`
- GradeBound + ℕ-polynomial wrappers:
  `LogOS/Complexity/ResourceSchemaGraded.agda`, `LogOS/Complexity/ObservabilityBudgetGraded.agda`
- Physical class interfaces + pipelines:
  Grade-native core:
  `LogOS/Complexity/PhysicsClassesWGraded.agda`, `LogOS/Complexity/PhysicsClassesWCostGuardsGraded.agda`,
  `LogOS/Complexity/PhysProofBridgeWGraded.agda`, `LogOS/Complexity/PhysProofBridgeWCostGuardsGraded.agda`,
  `LogOS/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda`,
  Kernel-native route (TruthRoute_Grade_Only-based): `Kernel` submodules inside the grade-native modules (re-exported by the wrappers),
  `LogOS/Complexity/PhysToTruthRouteBridge.agda`
- Example instantiation pack (UniversalIR): `LogOS/Complexity/UniversalIRCM.agda`

Examples
--------

- Example instantiation pack (UniversalIR): `LogOS/Complexity/UniversalIRCM.agda`
- SAT target surface: `LogOS/Complexity/Targets/SAT.agda` (includes `ClassicalETH`)
- SAT NP-completeness axiom pack: `LogOS/Complexity/Targets/SAT.agda`
  (module `ClassicalNPComplete`)
