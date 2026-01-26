<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

- Narrative-first aggregator: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
- Minimal proof-system interface: `LogOS/Syntax/ProofSystem.agda`
- Proof-search boundary (verification vs bounded search vs unbounded search): `LogOS/Domain/Complexity/ProofSearchBoundary.agda`
- Proof-search opacity spine (shared with GRH/opacity machinery): `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda`
  (general budgets via `ProofSearchOpacitySpine.For.Budgeted.General`;
   decode-ext budgets via `ProofSearchOpacitySpine.For.BudgetBy`;
   non-vacuity guard via `ProofSearchOpacitySpine.For.VacuityGuards`)
- Capstone (grade-native): `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`
- One-entry theorem (grade-native): `LogOS/Domain/Complexity/Targets/ProofSearchChainedTheoremGraded.agda`
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

- Conditional P/NP-shaped pack (grade-native interface): `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda`
- Canonical minimal route (info-theory): `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda`
  (`Assumptions`, `mkPack`)
- ℕ polynomial predicates can be lifted via `PvsNPFromInfo_Grade_Only.FromNat` (`PolyGrade.FromNat`).
- Classical P/NP interface (literature-aligned, ℕ-bound): `LogOS/Domain/Complexity/PvsNPLedger.agda`
- Reduction transport (many-one, poly-bounded): `LogOS/Domain/Complexity/Reduction.agda`
  (`Reduction.Classical.inPFromPolyReduction`, `Reduction.Classical.notInPFromPolyReduction`)
- Truth-route family: `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda` (grade-only, canonical).
  Uniform route: `TruthRoute_Grade_Only.Uniform`, `TruthRoute_Grade_Only.UniformNat`,
  and run-based `TruthRoute_Grade_Only.UniformNatFromRuns`;
  non-uniform adapters live in `TruthRoute_Grade_Only.NonUniform` / `TruthRoute_Grade_Only.NonUniformNat`.
- ETH-shaped assumption (uniform, ℕ-bound): `TruthRoute_Grade_Only.UniformNat.ETHAssumption`
  (SAT pack: `LogOS/Domain/Complexity/Targets/SAT.agda` module `ClassicalETH`).
- Optional non-degeneracy laws: `LogOS/Domain/Complexity/Model.agda` (module `StandardCMLaws`)

Information/physics routes
--------------------------

- Physics-of-information axiom packs:
  `LogOS/Domain/Complexity/LCUToLandauer.agda`,
  `LogOS/Domain/Complexity/SecondLaw.agda`,
  `LogOS/Domain/Complexity/MeasurementCapacity.agda` (record `NonUnitaryCapacity`),
  `LogOS/Domain/Complexity/DataProcessingInequality.agda`,
  `LogOS/Domain/Complexity/InfoProcessingBounds.agda`
  (curated surface: `LogOS/Packs/Complexity/Experimental/PhysicsOfInformation.agda`)

- Polynomial predicate + arithmetic helpers:
  `LogOS/Domain/Complexity/Poly.agda`, `LogOS/Domain/Complexity/PolyGrade.agda`,
  `LogOS/Domain/Complexity/Arithmetic.agda`
- Info bottleneck adapters and hardness bridge:
  `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda` (grade-native `FromLOB`),
  `LogOS/Domain/Complexity/InfoHardnessBridge.agda`
- Convenience pack: `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda`
- Grade-native resource schema and LOB packs:
  `LogOS/Domain/Complexity/ResourceSchemaG.agda`, `LogOS/Domain/Complexity/ObservabilityBudgetG.agda`
- GradeBound + ℕ-polynomial wrappers:
  `LogOS/Domain/Complexity/ResourceSchemaGraded.agda`, `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda`
- Physical class interfaces + pipelines:
  Grade-native core:
  `LogOS/Domain/Complexity/PhysicsClassesWGraded.agda`, `LogOS/Domain/Complexity/PhysicsClassesWCostGuardsGraded.agda`,
  `LogOS/Domain/Complexity/PhysProofBridgeWGraded.agda`, `LogOS/Domain/Complexity/PhysProofBridgeWCostGuardsGraded.agda`,
  `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda`,
  Kernel-native route (TruthRoute_Grade_Only-based): `Kernel` submodules inside the grade-native modules (re-exported by the wrappers),
  `LogOS/Domain/Complexity/PhysToTruthRouteBridge.agda`
- Example instantiation pack (UniversalIR): `LogOS/Domain/Complexity/UniversalIRCM.agda`

Examples
--------

- End-to-end info-route skeleton: `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda`
- Example UniversalIR instantiation shell: `LogOS/Domain/Complexity/Examples/InfoRouteChain.agda` (module `UniversalIR`)
- Golden-path scaffold (grade-native → bridge → classical): `LogOS/Domain/Complexity/Examples/GoldenPath.agda`
- Minsky scheme instantiation (machines-as-schemes factoring; Flow g = simulate (budget g)):
  `LogOS/Domain/Complexity/Examples/GoldenPath.agda` (module `Minsky`, includes `ScaleOps`-based budget hardening)
- SAT target surface: `LogOS/Domain/Complexity/Targets/SAT.agda` (includes `ClassicalETH`)
- SAT NP-completeness axiom pack: `LogOS/Domain/Complexity/Targets/SAT.agda`
  (module `ClassicalNPComplete`)
