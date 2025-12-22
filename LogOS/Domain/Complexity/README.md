<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Complexity Layout
=================

Publication-facing entrypoint
-----------------------------

- Narrative spine: `docs/Complexity.lagda.md`
- Namespaced wrapper (safe surface): `LogOS/Models/Complexity/Core.agda`

Main modules (this directory)
-----------------------------

- Narrative-first aggregator: `LogOS/Domain/Complexity/ProofSearchSeparation.agda`
- Minimal proof-system interface: `LogOS/Domain/Complexity/ProofSystem.agda`
- Proof-search boundary (verification vs bounded search vs unbounded search): `LogOS/Domain/Complexity/ProofSearchBoundary.agda`
- Capstone (grade-native): `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`
- One-entry theorem (grade-native): `LogOS/Domain/Complexity/Targets/ProofSearchChainedTheoremGraded.agda`
- DetWithin route (kernel-friendly abstraction): `ProofSearchCapstoneGraded.DetWithinRoute`

Pack conventions
----------------

- Most routes expose a standard quartet: `Assumptions`, `Claim`, `Pack`, `mkPack`.
- `Pack.claim` is the canonical way to extract the claim from assumptions.

P/NP interfaces and bridges
---------------------------

- Conditional P/NP-shaped pack (grade-native interface): `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda`
- Canonical minimal route (info-theory): `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda`
  (`Assumptions`, `mkPack`)
- ℕ polynomial predicates can be lifted via `PvsNPFromInfo_Grade_Only.FromNat` (`PolyGrade.FromNat`).
- P/NP pack (language-relative, packaging only): `LogOS/Domain/Complexity/PvsNP.agda`
- Classical P/NP interface (literature-aligned, ℕ-bound): `LogOS/Domain/Complexity/ClassicalPvsNP.agda`
- Truth-route family: `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda` (grade-only, canonical),
  `LogOS/Domain/Complexity/TruthRoute.agda` (ℕ-bound via `gradeBound`, deprecated compat; includes witness-size refinement under `TruthRoute.For.WithWitnessSize`)
- Optional non-degeneracy laws: `LogOS/Domain/Complexity/StandardCMLaws.agda`

Information/physics routes
--------------------------

- Polynomial predicate + arithmetic helpers:
  `LogOS/Domain/Complexity/Poly.agda`, `LogOS/Domain/Complexity/PolyGrade.agda`,
  `LogOS/Domain/Complexity/Arithmetic.agda`
- Info bottleneck adapters and hardness bridge:
  `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda` (grade-native `FromLOB`),
  `LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded.agda` (grade-bound `FromLOBGradePG`, compat `FromLOB`),
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
- Example UniversalIR instantiation shell: `LogOS/Domain/Complexity/Examples/InfoRouteChainIR.agda`
- Golden-path scaffold (grade-native → bridge → classical): `LogOS/Domain/Complexity/Examples/GoldenPath.agda`
- Minsky scheme instantiation (machines-as-schemes factoring; Flow g = simulate (budget g)):
  `LogOS/Domain/Complexity/Examples/GoldenPathMinsky.agda` (includes `ScaleOps`-based budget hardening)
