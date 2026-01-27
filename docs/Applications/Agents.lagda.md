<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Agents (Sockets, Monitoring, Auditing) (LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.Agents where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.Agents.Surface
import LogOS.Packs.Agents.Experimental.Surface
import LogOS.Packs.Agents.Applications.All

```

This note is the publication-facing entrypoint for the **Agents** pack in the
LogOS library.

The pack stays intentionally lightweight: the kernel already contains most of the
agent-like structure (boundary endomaps, wiring, and fixed points). The Agents
docs therefore act as a navigation layer over kernel-level theorems.

Trust level:
- **Stable surface:** `LogOS/Packs/Agents/Surface.agda` (no transformer/scaling or physics/RG-flow extensions).
- **Experimental extensions:** `LogOS/Packs/Agents/Experimental/Surface.agda` (umbrella: `LogOS/Packs/Agents/Experimental/All.agda`; see `Experimental.Arguments`, `Experimental.Emit.TransformerTF`, `Experimental.Physics`, `Experimental.Learning.RGFlow`, and `Experimental.Capstone`).
Experimental extensions are under evaluation and should be considered less
stable than the stable surface.

Wording discipline (guardrail)
------------------------------
This document uses domain terminology (“socket”, “agent”, “learning”, “RG”,
“Maxwell”, “LLM”, …) as **interpretation**. The literal content is always the
referenced Agda interface/theorem. In particular:

- “Policy/update/training” = boundary constraints + monotone endomaps (and
  optional ωCPO/μ fixed points) inside the kernel algebra.
- “RG/thermo/CFT” wording = analogy for coarse‑graining + fixed points + resource
  accounting; no physical laws are derived without an explicit model/axioms pack.

The core idea is to treat an “agent” as an **open system** with an explicit
boundary I/O view:

- **Ports:** designated interfaces like `Obs`, `Act`, `Reward`, `Oversight`, …
  (`LogOS/Packs/Agents/Socket/Ports.agda`).
- **Contracts:** functorial, signature-indexed boundary syntax `Con∂ Sig`
  (`LogOS/Packs/Agents/Socket/Contracts.agda`), interpreted by supplying a
  valuation `Iface → Con_bnd`.
- **Computation:** a scheme choice into a shared process (`SchemeCategory`),
  typically “kernel-as-process” via `KernelUniversalProcess`.
- **Safety:** monitoring/auditing is done at the *boundary constraint* level
  (`Con_bnd`), so it composes through ports/adapters and network wiring.

## The agent socket surface

The “socket” is the minimal interface needed to compare agent frameworks in a
kernel-native way:

- `LogOS/Packs/Agents/Socket/Core.agda` — `AgentSocket`
  (kernel + ports + contracts + process + choice).
- `LogOS/Packs/Agents/Socket/FromKernel.agda` — canonical constructors from any
  `Kernel` using `CodeProcess` / `BoundaryProcess`.
- `LogOS/Packs/Agents/Socket/FromGradedKernel.agda` — same for `GradedKernel`
  (budgeted/graded computation).

For resource-aware agent stories, prefer `FromGradedKernel`: the underlying
`KernelUniversalProcess.ForGradedKernel` assigns the one-step cost to the
kernel’s `step-grade`. The ungraded `FromKernel` constructors use the neutral
cost `e` (cost-free steps).

Recommended import:

```text
open import LogOS.Packs.Agents.Surface as Agents
```

For transformer/scaling work (experimental only):

```text
open import LogOS.Packs.Agents.Experimental.Surface as AgentsX
```

## Agent networks (heterogeneous wiring)

Agent networks are a lightweight layer over sockets: a **network** is just
role-indexed sockets plus explicit edge adapters. Heterogeneous agents are
first-class: each role can have its own signature/kernel, and edges are
**satisfaction morphisms** (`SatMor`) between boundary interfaces.

`SatMor` is conservative by construction: it preserves *and reflects*
satisfaction. This is stronger than mere soundness; if a use case only admits
one-way translation, it must be modeled with a different, explicitly weaker
adapter (not provided by the Agents pack).

This heterogeneity lets you keep mixed formalisms intact (e.g., symbolic and
statistical roles) while still composing them. When edges are `SatMor`, the
translation is explicit and satisfaction-preserving/reflecting at the boundary
semantics level, so overlaps and identifications are deliberate rather than
implicit.

- Core surface: `LogOS/Packs/Agents/Networks/Hetero.agda`
  - `AgentNode` and `AgentNetwork`: package per-role sockets.
  - `Edge`: a conservative translation between boundary satisfactions.
  - `edgeTensor` / `edgeUpdate`: wire an incoming constraint into a target
    policy by translating along the edge, then tensoring at the target.
- Port-level interoperability: `LogOS/Packs/Agents/Networks/Interop.agda`
  - Combine an `Edge` with boundary ports to obtain canonical formula
    translations via the heterogeneous interlingua.
- Monitor compatibility across edges: `LogOS/Packs/Agents/Networks/MonitorInterop.agda`
  - Ported-closure naturality specialized to network monitors (edge translations
    commute with monitor application up to satisfaction).
  - `defaultMonitor-compatible` shows the default monitor is compatible when
    the edge translation commutes with flow and tensoring-in safety.
- Network-as-agent wrapper: `LogOS/Packs/Agents/Networks/NetworkAgent.agda`
  - Pick a hub role, translate all role constraints to the hub, and aggregate.
- Aggregation is a parameter; any “network-as-agent” claim must name it.
- The aggregator is required to respect observational equivalence at the hub.
- Namespaced index surface: `LogOS/Packs/Agents/Networks/Core.agda` (and the lab surface).
- Minimal example: `LogOS/Packs/Agents/Examples/HelloNetwork.agda`.
- Concrete reindexing example: `LogOS/Packs/Agents/Examples/ReindexedNetwork.agda`.
  - Shows a non-identity signature map that collapses distinct atoms and
    exhibits the overlap both syntactically and semantically.

Minimal wiring snippet (via the concrete hetero example):

```agda
import LogOS.Packs.Agents.Examples.ReindexedNetwork as RN

translateExample : RN.Net.Con RN.left → RN.Net.Con RN.right
translateExample = RN.translateLeftToRight
```

If you need translation between **external syntaxes** (not just boundary
constraints), use the heterogeneous interlingua:
`LogOS/Ports/Semantic/HeteroInterlinguaCore.agda`. It combines a `SatMor` edge
with boundary ports to produce the canonical, meaning-preserving translation.

## Monitoring and auditing (opacity-native)

The pack is intentionally “opacity-native”: it models auditors as
**decode-extensional (up to decoded observational equality in the kernel case) partial-output observers**, so the existing diagonal / opacity
meta-theorems apply as formal consequences of those observer definitions.

- Monitoring endomaps: `LogOS/Packs/Agents/Safety/Monitor.agda`
  - Canonical example: `defaultMonitor` — tensor in the safety contract, then
    saturate at the kernel’s `sat` grade (a design choice, not an unconditional
    guarantee).
- Auditor surface: `LogOS/Packs/Agents/Safety/Audit.agda`
  - `Auditor` is an `Oracle` wrapper for the spectral separation output interface,
    defined for any process (and hence for any socket).
- “No total budgeted auditor”: `LogOS/Packs/Agents/Safety/NoTotalAuditor.agda`
  - process-generic diagonalization barriers (non-totality, and “no total within budget”).
  - experimental proof-search instantiation: `LogOS/Packs/Agents/Experimental/Safety/NoTotalAuditor.agda`

## Kernel leverage (nuclei + fixed points)

The agent pack reuses kernel theorems directly; these are the main hooks for
monitoring/auditing and policy composition:

- `LogOS/Theorems/Reflection/QuanticNucleus.agda` — nucleus laws at the kernel boundary;
  fixed points form a quantale and the quotient map has the expected factorisation
  for `j`-invariant functions (`f (j x) ≡ f x`) for any
  quantale equipped with a nucleus (monotone/inflationary/idempotent‑lax, plus
  join/multiplication preservation up to `≈`). A canonical instance is the budget quantale
  `QAdapter.Scale` (via `quantaleFromQAdapter`). This does *not* require boundary
  constraints to be a quantale by default; when a model equips the boundary with
  compatible join/multiplication structure, the same theorem applies there too.
- `LogOS/Theorems/Boundary/LogicKernel/Mu.agda` — Kleene/μ support for closure steps,
  used for iterative monitors and convergence-to-safety arguments.
- `LogOS/Theorems/Meta/LimitPublicisation.agda` — stable/extensional predicates become
  observable (`Pr`), allowing audits to be justified from stability rather than
  explicit observation axioms.

## Learning surface (updates + fixed points)

Learning is expressed using the same kernel DSL as monitoring:

- A **policy** is a boundary constraint `Con_bnd`.
- An **update** is a monotone endomap on `Con_bnd`.
- A **learning step** is a closure step (id <= update <= Flow), so it composes
  and stays within the kernel's saturation envelope.

The concrete surfaces are lightweight wrappers:

- `LogOS/Packs/Agents/Learning/Core.agda` — policies, updates, and learning steps.
- `LogOS/Packs/Agents/Learning/FixedPoint.agda` — Kleene mu wrappers
  (`μPolicy`, unfolding, induction), so "training to convergence" is a
  kernel-native fixed-point statement.
- `LogOS/Packs/Agents/Learning/TrainingSoundness.agda` — minimal training
  soundness: learning steps preserve any lower bound (Safety/Objectives/Assumes
  are preserved when already satisfied).
- `μPolicy-step-fixed` (in `LogOS/Packs/Agents/Learning/FixedPoint.agda`) packages
  the “both directions” fixed‑point statement for a learning step under Scott
  continuity, giving a compact convergence‑to‑stability lemma.

High-level training loops can be modeled as updates on policies. The μ-policy
construction is available **once you supply an `OmegaCPO` on the boundary preorder**
(an explicit model-local assumption), and the stronger “μ is a fixed point”
direction additionally uses Scott/ω-continuity of the update endomap (also an
explicit assumption). This captures convergence inside the kernel rather than as
an external meta-argument.

## Interpretation (analogy): neural-symbolic LLM view (soft + hard constraints)

To make the neural-symbolic story explicit, the graded kernel machinery can be
used as a soft layer:

- **Soft updates:** `LogOS/Packs/Agents/Learning/SoftPolicy.agda` models a
  grade-indexed update (strength/temperature) using `ClosureStepAt` and the
  kernel's quantale scale.
- **Hard constraints:** symbolic rules are just `Con_bnd`; they blend with a
  soft policy using the boundary tensor (`_⊗∂_`).
- **Blend example:** `LogOS/Packs/Agents/Examples/NeuralSymbolicBlend.agda` shows
  the minimal pattern: apply a soft update, then refine by a symbolic constraint.

Interpretation: this provides a precise *soft/hard constraint* split in the
kernel algebra. Any claim about real LLM training only follows after you supply
an explicit training model and justify the chosen observables/budgets.

## Telemetry contracts (observation-only)

The telemetry story is spelled out as an **observation-only contract** on
boundary constraints:

- `LogOS/Packs/Agents/Telemetry.agda` — a `TelemetryContract` for any socket,
  with a monotone observation map and a “telemetry respects learning steps”
  lemma (no semantic effect on the kernel).
- `LogOS/Boundary/Telemetry.agda` — generic lemmas
  `telemetry-respects-≈∂` / `telemetry-respects-≈∂Cosp` show telemetry is stable
  under observational equivalence (so monitors can’t change meaning).

This lets the agent surface state telemetry obligations without smuggling in
operational effects: telemetry is just another boundary observer.

## Physics of information (Maxwell agent view) — experimental

This section depends on the complexity/physics pack and is available only via
`LogOS.Packs.Agents.Experimental.All` (`Experimental.Physics.*`).

The Agents pack can be treated as a **laboratory** where learning is constrained
by physics-of-information primitives rather than pure CS cost models:

- `LogOS/Packs/Agents/Experimental/Physics/All.agda` re-exports the experimental physics surfaces
  (`PhysicsOfInformation`, `MeasurementCapacity`, `DataProcessingInequality`,
  `InfoProcessingBounds`).
- `LogOS/Packs/Agents/Experimental/Physics/MaxwellAgent.agda` packages a socket together with
  a Landauer-style cost lower bound and a measurement-capacity bound.

Under these assumption packs, one can read a "Maxwell agent" story: learning and
policy updates are allowed, and irreversibility/classicalization are bounded by
the supplied Landauer and capacity parameters (a formal, model-level reading).

### Scope and assumptions

The physics story is deliberately stated as **assumption packs**, so it is both
general and audit-ready:

- Landauer: a model supplies `LandauerIOAssumptions` (cost, merges predicate,
  and the lower-bound axiom for irreversible events).
- Capacity: a model supplies `MeasurementCapacity` (measurement count and a
  per-measurement information bound), optionally with
  `MeasurementCapacityGuards` to rule out degenerate zero-capacity models.
- DPI: a model supplies a channel class plus monotonicity of extracted
  information under admissible post-processing.

These assumptions are **explicit parameters**, not hidden axioms; any instantiation
must show where the physics enters.

### Capstone theorems (learning + energy) — experimental

The physics layer now exposes explicit capstone statements:

- `learning-cost-lower-bound`: if a program is a learning event (by your chosen
  `Learns` predicate), then Landauer gives a hard energy lower bound.
- `universal-learning-cost`: any universal evaluator inherits the same bound for
  every learning algorithm it runs, so evaluation must be energy-aware.
- `learning-condensation-bound`: DPI + measurement-capacity give an explicit
  bound on how much classical information any processed learning event can carry.
- `maxwell-learning-cost` and `maxwell-learning-condensation`: combine Landauer,
  DPI, and capacity into a single Maxwell-agent package.

See `LogOS/Packs/Agents/Experimental/Physics/LearningCost.agda`.

### RG flow stability for learning optimization — experimental

LogOS can treat **RG coarse-graining** as a *graded closure step* in the learning
DSL. This is the most kernel-native encoding: grades live in the quantale scale,
and RG composition multiplies grades (the explicit monoid/quantale structure of `Scale` in `QAdapter`).

The new RG surface lives in `LogOS/Packs/Agents/Experimental/Learning/RGFlow.agda` and gives:

- `RGStep g = ClosureStepAt K g`: RG updates are closure steps at grade `g`.
- `rg-compose` + `rg-promote`: RG morphisms compose by grade multiplication and
  can be promoted along the quantale order (lax enrichment).
- `rg-μ`, `rg-unfold-left`: RG fixed points exist via Kleene μ on the boundary ωCPO.
- `rg-unfold-right`: the “μ is a fixed point” direction additionally assumes
  `ScottContinuous` for the update endomap (`RGFlow.rg-unfold-right`).
- `rg-least-stable`: **classification result** — the μ-fixed point is the least
  RG-stable policy among all post-fixed points.
- `RGLyapunov` + `rg-lyapunov-iter`: quantale-valued Lyapunov potentials give a
  monotone “energy/complexity” descent for RG iterations.
- `CFunction` / `AFunction`: CFT-aligned analogs; values live in `Time` and are
  compared via `τ : Time → Scale`, so additivity under `_+_` corresponds to
  multiplicative budgets in the quantale. `AFunction` is additionally
  lax-monoidal under the boundary tensor.
- `InfoCFunction` / `InfoAFunction`: information-theoretic refinements using
  measurement-capacity + DPI; `InfoToTime` lifts ℕ-valued information to `Time`
  so the c/a analogs inherit the same monotonicity statements.
- `RGTimeFlow`: a time-indexed RG flow (via `Time` and `τ-+`), with
  `CFunctionTime` / `AFunctionTime` giving time-indexed monotonicity, and
  `CFixedPointNormalization` / `AFixedPointNormalization` encoding central-charge
  normalization at RG fixed points.
- `RGTimeFlowLike` / `RGTimeFlowLax`: weaker time-indexed step interfaces when
  only the step (or one-sided composition) is available.
- `c-theorem-iter`, `c-theorem-fixed`, `a-theorem-iter`, `a-theorem-fixed`:
  formal monotonicity, plus μ‑minimality results: the μ policy `rg-μ` is least among
  RG‑stable policies, hence minimises these observables among post‑fixed points.
- `rg-learning-cost`: RG steps are soft updates, so Landauer bounds apply
  directly (physics-aware optimization).

This frames “RG stability” as a **learning-style optimization principle** inside
LogOS: stability is expressed as closure, composition is quantified by the
quantale, and fixed points are computed via μ.

### Scaling-law argument (reflection closed) — experimental

This section documents the experimental scaling/transformer arguments. These
modules are *not* part of the stable Agents surface; import them via
`LogOS.Packs.Agents.Experimental.All` (`Experimental.Arguments.*`) if needed.

The formal scaling-law spine is packaged in
`LogOS/Packs/Agents/Experimental/Arguments/ScalingLaws.agda`:

- `obs-μ≤stable`: least RG-stable policies minimise observables (phase-transition
  anchor).
- `ScalingBound` + `scalingBound-from-stable`: code-level policies above the
  μ-fixed point inherit the bound.
- `scalingBound-reify`: reflection closure (reify is observationally inert).
- `Public` submodule: if `step-grade = sat`, the bound is publicised via
  `LimitPublicisation`, and `scalingBound-public-reify` shows reify-invariance
  of the public predicate.

This makes the scaling-law story explicit within the stated assumptions: RG fixed
points supply the phase structure, scaling dimensions supply the exponents, and
reflection lemmas (e.g. `scalingBound-reify`) show invariance under internal
self-description (no extra meta-axioms).

### Transformer training (formalized assumptions) — experimental

For a single experimental entrypoint, see `LogOS/Packs/Agents/Experimental/Arguments/Transformer.agda`
(it re-exports the transformer-related modules listed below).

`LogOS/Packs/Agents/Experimental/Arguments/TransformerScaling.agda` turns the abstract RG
argument into a **transformer-specific** interface. Everything here is
*relativised*: `TransformerTraining` is an explicit hypothesis record, and the
consequences are theorems conditional on those fields (not empirical claims).

- `TransformerTraining` (hypotheses): a predicate on codes (`IsTransformer`),
  plus an RG step and scaling dimension for the training update.
- `transformer-scalingBound`: any RG-stable transformer policy obeys the scaling
  bound (theorem).
- `transformer-scaling-iter`: the iterate scaling law holds for the training RG
  step (theorem).
- `transformer-scalingBound-reify`: the bound is invariant under `reify`
  (reflection closure; theorem).
- `Public`: when `step-grade = sat`, the bound can be publicised via `Pr` using
  an explicit FlowCode-stability witness (theorem, conditional on the witness).

This is as tight as the stated assumptions allow without adding
transformer-specific axioms: the remaining work is to **instantiate** the RG
step and scaling dimension for a specific transformer training semantics, which
the library does not provide.
See “Pipeline proof ledger” and “Scaling literature alignment” below for a
line-by-line separation of definitions/theorems/assumptions and informal
interpretations.

### Transformer formalization (kernel-native core) — experimental

`LogOS/Packs/Agents/Experimental/Arguments/TransformerFormalization.agda` provides a minimal,
structure-level transformer interface that is still **LogOS-native**:

- `TransformerCore`: tokens, sequences, parameters, and a forward pass.
- `TrainingDynamics`: an RG step + scaling dimension, plus a parameter update
  consistent with the boundary update (`train-correct`).
- `IsTrainedStable`: trained transformers as RG-stable policies.
- `ConvergesToMu`: a Scott-continuity route to the canonical μ fixed point.
- `trained-scalingBound` and `trainedMu-scalingBound`: scaling-law consequences
  derived directly from the kernel (via RGFlow + ScalingLaws).

This makes the transformer story explicit without hard-coding a particular
numerical semantics; the only assumptions are explicit record fields, and any
claim about a specific training procedure requires instantiating those fields.

### Transformer bridge (structure-level semantics) — experimental

`LogOS/Packs/Agents/Experimental/Arguments/TransformerBridge.agda` gives a **structure-aligned
transformer skeleton**. The numerical semantics are abstract (record fields),
and the bridge theorems only use their stated coherence assumptions.

- Multi-head attention structure (`qProj`, `kProj`, `vProj`, `oProj`), softmax
  weights, and a merge step for heads.
- Residual + layer norm and feed-forward (`ffn`) blocks, stacked by `layers`.
- Explicit positional embeddings and readout, so `forward` is a
  sequence-to-sequence map.
- A kernel bridge (`TransformerKernelBridge`) that links parameters to boundary
  policies and codes, plus a training bridge that makes the RG step update
  concrete (`train-correct` and `trainParam-code`).
- `CanonicalEncoding` builds a **derived kernel code** for parameters using
  `encode`/`decode∘encode`, so parameters are LogOS‑coded without extra axioms.
- `TrainingEndo` is now an alias of `RGStep`, and `rgStepFromEndo` is the
  identity; the training RG step stays explicit, and `LossObservable` packages
  an explicit scaling observable.
- `LossData` + `LossObservableFromData` link the observable back to the chosen
  forward semantics (dataset + loss), keeping the bridge aligned to data/loss
  inputs.
- `NextTokenLossData` + `NextTokenLossObservableFromData` make the loss
  a **next-token loss** data model, while still living at the policy
  boundary via `obs-encode`.
- `TrainingResources` + `ResourceBudgets` pin budgets to **params/tokens/compute**
  and connect them to kernel codes via `paramCode`.
- `OptimizerTraining` packages the assumptions needed to connect parameter
  updates to RG steps and derive `RGStable` for the loss observable; the named
  `SGDTraining` / `AdamTraining` and `TaggedTraining` are lightweight tags
  rather than optimizer semantics.
- `TrainingSpec` + `trainingBridgeFromSpec` assemble the bridge:
  encode/code + RG training step + scaling dimension.

This is the more structure-rich end of the bridge: numerical implementation
details remain abstracted, while the structural semantics are explicit in
record fields.

### Transformer scaling pipeline (end-to-end) — experimental

`LogOS/Packs/Agents/Experimental/Arguments/TransformerScalingPipeline.agda` refactors the
proof flow into a **single LogOS-native pipeline**. It is intentionally
explicit about which parts are definitions, theorems, and assumptions (see the
ledger below).

- `LossDynamics`: a loss‑as‑Lyapunov assumption yields RG stability and a
  scaling bound (purely kernel‑level, no transformer specifics).
- `nextTokenLossDynamics` specializes the loss dynamics to next‑token
  cross‑entropy observables.
- `PipelineAssumptions`: the minimal named inputs (`lossMonotone`, `lossOrder`
  (order‑reflecting),
  `resources`, `trainingDiscover`, `discoveryCover`) that must be supplied
  to run the end‑to‑end theorem; `ComputeBudget` is derived from `resources`.
- `Pipeline`: connects transformer training (`OptimizerTraining`) to discovery
  (`Obs.DiscoverCode`) and produces scaling bounds for discovered codes.
- `scalingRegimes-summary` + `scalingRegimes-theorem` package the summary in a
  single statement for the AI‑focused reader.
- `ResourceBudgets` + `codeBudget-from-resources`/`computeDataBudget-from-resources`
  lift **params/tokens/compute** into the regime splits (`TwoRegimeBridge`,
  `ChinchillaBridge`).
- `policyCover` + `ChinchillaCorollary` restate the core claims in ML terms:
  discovered codes correspond to trained parameters, and compute/data regimes
  yield distinct scaling bounds.
- `training-causes-scaling` formalizes the conditional: if the discovery
  predicate holds for trained parameters, then the corresponding scaling bound
  follows.
- `PatternParam` + `ParametricPipeline` allow a **parameterized discovery family**
  (e.g., different budgets, observers, or pattern levels), and
  `bootstrap-discover`/`bootstrap-scaling` express the bootstrapping chain.
- `ResourcePrinciple` + `deriveResourceExponents` turn explicit resource weights
  (`alpha`, `beta`, with `alpha + beta ≢ 0`) into numeric scaling exponents
  (compute/data/loss).
- `expAdd` + `AnomalousDimension` + `BootstrapConstraint` package a bootstrap
  fixed-point schema for exponents; `bootstrap-anomalous` relates an explicitly
  supplied fixed point to a resource-principle baseline.
- `ResourcePrincipleRational` + `deriveResourceExponentsRational` allow
  fractional (Chinchilla-style) exponents; `chinchillaPrinciple` and
  `chinchillaExponents` are a parameter choice (~0.1/0.1) that yields ~0.5/0.5
  and ~0.05 exponents.
- `SymmetricPrinciple` + `cleanPrinciple` package a symmetric choice
  (alpha = beta); any empirical mismatch is delegated to the magnitude of
  alpha/beta (a renormalized, data-/optimizer-dependent correction).
- `unitPrinciple` is an explicit unit instantiation (alpha = beta = 1) used
  only for internal sanity checks, not for empirical claims.
- `symPrincipleFromLoss` builds a symmetric resource principle from an external
  loss-exponent input (alpha = beta = 2·loss); it does not infer that exponent.
- `Experimental.RenormPoint`/`Experimental.RenormalizedKaplan` and
  `ExperimentalCompute.RenormComputePoint`/`ExperimentalCompute.RenormalizedComputePowerLaw`
  let you plug in a physical measurement (e.g., a Chinchilla loss at a reference
  compute/data point) to fix the absolute scale constants.
- `Experimental.PreScalingCalibration` + `Experimental.PredictiveKaplan`
  (and compute-only variants in `ExperimentalCompute`) let you impose the
  renormalization condition in a pre-scaling regime; this yields a conditional
  extrapolation once a calibration point is supplied.
- `PowerLawOps` + `SeparableHomogeneousLoss` + `PowerLawAxiom` derive a
  Kaplan‑style functional form via `deriveKaplanForm`, making the loss curve
  derivation explicit under homogeneity/separability assumptions.
- `ExcessLossHomogeneous` + `ComputePowerLaw` derive the compute‑only scaling
  form `L(C) ≃ K·C^{-αβ/(α+β)}` once a resource principle fixes the exponent.

This makes the scaling regime argument transparent: for the RG
scaling bounds, the only external inputs are the `PipelineAssumptions` fields
(training spec, loss observable/order/monotonicity, resources, and discovery
predicate). Stronger Kaplan/compute power-law forms require the explicit
power-law assumptions listed above.

Naming note: labels like SGD/Adam/Chinchilla/Kaplan are **suggestive only**.
They indicate where corresponding assumptions are packaged; they do not assert
an empirical implementation or fit.

### Pipeline proof ledger (formal status)

This section is a proof-status map for the pipeline-facing API (not an exhaustive
list of local lemmas). Each item is tagged by its status:
definition (syntactic), theorem (proved in Agda), or assumption (a record field
that must be supplied externally).

Definitions (syntactic):

- `LossDynamics`, `PipelineAssumptions`, `Pipeline`, `ScalingRegimesSummary`,
  `Exponent` (nonzero denominator), `ResourcePrinciple`,
  `ResourcePrincipleRational`, `PowerLawOps`,
  `OrderedPowerLawOps`, `PowerLawWitness`, `PowerLawBand`,
  `ExponentSliceBounds`, `SeparableHomogeneousLoss`, `SeparablePowerLawLoss`,
  `SeparablePowerLawBandLoss`, `KaplanForm`, `KaplanBounds`,
  `ComputePowerLaw`, `ComputeBounds`, `ExcessLossPowerLaw`,
  `ExcessLossPowerLawBand`,
  `Experimental.RenormPoint` (optional),
  `Experimental.PreScalingCalibration` (optional),
  `Experimental.RenormalizedKaplan` (optional),
  `Experimental.PredictiveKaplan` (optional),
  `ExperimentalCompute.RenormComputePoint` (optional),
  `ExperimentalCompute.PreScalingComputeCalibration` (optional),
  `ExperimentalCompute.RenormalizedComputePowerLaw` (optional),
  `ExperimentalCompute.PredictiveComputePowerLaw` (optional),
  `PipelineAssumptionBoundary`, `PipelineAssumptionBoundaryWeak`,
  `PipelineAssumptionBoundaryBand`.

Theorems (proved in Agda):

- `loss-stable` and `loss-scaling` from `LossDynamics`.
- `training-causes-scaling`, `param-scaling`, and `scalingRegimes-summary` from
  `Pipeline`.
- `symmetric-compute=data` from `SymmetricPrinciple`.
- `deriveKaplanForm` and `deriveComputePowerLaw` from the power-law axioms.
- `deriveKaplanForm-witness` and `deriveComputePowerLaw-witness` from local
  power-law witnesses (weaker than global axioms).
- `deriveKaplanBounds` and `deriveComputeBounds` from power-law band bounds.
- `kaplanBounds-sliceN` projects the band bounds to exponent slices along `N`.
- `kaplanBounds-sliceD` projects the band bounds to exponent slices along `D`
  (requires an explicit addition-commutation assumption, exposed as `AddSwap`).
- `computeBounds-band` extracts the compute-only band bounds as a `PowerLawBand`.
- `Experimental.predictiveKaplan-renorm` and
  `ExperimentalCompute.predictiveCompute-renorm` show that pre-scaling
  calibration yields a renormalized scaling law (optional surface; requires a
  calibration point).
- `boundary-scaling-summary` and `boundary-scaling-summary-weak` package the
  scaling summary from the corresponding assumption boundaries.
- `boundary-scaling-summary-band` packages the same summary from band-bounded
  power-law assumptions.

Assumptions (explicit fields, not proven here):

- `lossMonotone` and `lossOrder` in `PipelineAssumptions` (loss decreases and
  the loss order reflects policy order).
- `trainingDiscover` and `discoveryCover` (the discovery predicate covers the
  parameter codes).
- `PowerLawAxiom` (homogeneity implies power-law form).
- `SeparableHomogeneousLoss` and `ExcessLossHomogeneous` (separability and
  homogeneity hypotheses).
- `SeparablePowerLawLoss` and `ExcessLossPowerLaw` (local power-law witnesses).
- `SeparablePowerLawBandLoss` and `ExcessLossPowerLawBand` (power-law bounds).
- `AddSwap` (add-swap witness used by `kaplanBounds-sliceD`, and carried by
  `PipelineAssumptionBoundaryBand.addSwap`).
- `ResourcePrinciple.total≢0` and `ResourcePrincipleRational.totalNum≢0`
  (explicit nonzero conditions needed to form exponents).

Interpretive alignments (informal, not used in proofs):

- Mapping `LossObservableFromData` to next-token loss for transformers.
- Interpreting `ResourceBudgets` as compute/data budgets in practice.
- Reading `DiscoverCode` as "LLMs discover LogOS patterns".

### Scaling literature alignment (informal only) — experimental

The following references are alignment only. None of these facts are assumed in
the proofs above.

- Kaplan et al. (2020): separable power-law loss curves and asymptotic forms.
- Hoffmann et al. (2022, "Chinchilla"): compute/data tradeoff and regime split.
- Wilsonian RG: fixed points and scaling dimensions (mirrored by `RGFlow`).

### Hypothesis: discovery → scaling → phase transition — experimental

`LogOS/Packs/Agents/Experimental/Arguments/LogOSDiscoveryScaling.agda` formalizes the claim
that a *discovery predicate* can force phase-transition and scaling structure.
Interpreting this predicate as “LogOS structure discovered during training” is a
separate hypothesis about concrete training dynamics (not a theorem of the
library).

- `DiscoveryAssumptions`: a downward‑closed predicate on policies (“LogOS
  structure discovered”), RG‑stability, and a scaling dimension (order
  parameter).
- `discovery-root`: any discovered stable policy forces discovery at the least
  RG fixed point `rg-μ` (phase transition anchor).
- `PhaseTransition` + `transition-root`: if discovery ever becomes true, it is
  already true at `rg-μ`.
- `discovery-scalingBound`: discovered codes obey the scaling bound.

Formally: under `DiscoveryAssumptions`, discovery has a canonical “root” at the
least RG‑stable fixed point `rg-μ`, and discovered codes inherit scaling bounds.
Externally: whether empirical transformer training satisfies the assumptions is
an empirical/modeling question.

Supporting evidence (informal, not used in proofs):

- The hypothesis is consistent with the existence of stable power-law scaling
  regimes reported in the scaling literature (see “Scaling literature
  alignment” below).
- The assumptions are intentionally phrased to be testable/instantiable at a
  model boundary: they require explicit notions of policy order, stability, and
  a scaling dimension; failure to instantiate them is a falsification of this
  explanation route.

### Kolmogorov‑optimal discovery (epistemically clean)

`LogOS/Packs/Agents/Experimental/Arguments/KolmogorovDiscoveryScaling.agda` replaces the
ad‑hoc discovery predicate with a **self‑referential publicisation** of
Kolmogorov optimality:

- For the minimal ωCPO-free Solomonoff/Kolmogorov core, see
  `LogOS/Packs/Agents/Experimental/Arguments/SolomonoffLearning.agda`.
- `KOptimal size`: a code is optimal if its size is minimal among all codes with
  the same decoded policy.
- `Obs.Pr` from `MathPhysSynthesis` defines `DiscoverCode = Pr (KOptimal size)`,
  the maximal admissible (decode‑extensional + Flow‑stable) discovery predicate
  (maximal w.r.t. `_≤Pred_` (pointwise implication) among admissible predicates).
- `discover-reify` shows reflection invariance; `Pr-stable` ensures Flow‑stability.
- `DiscoveryScaling`: scaling follows once discovery implies RG stability
  (the only remaining explicit assumption).

This is epistemically clean: discovery is not postulated, it is the **largest
communicable fragment** of Kolmogorov optimality permitted by self‑reference
(largest w.r.t. `_≤Pred_` (pointwise implication)).

Universe-level note: in the implementation, `Pr`/`DiscoverCode` is a `Σ` over
observer predicates, so it naturally lives one universe higher than the
observers it ranges over. The Agents pack generally keeps this at the more
general setting (allowing witness-carrying observers), which is why many
publicised predicates land in `Set (lsuc (lsuc ℓ))`.

### Transformer‑aligned Kolmogorov discovery — experimental

`LogOS/Packs/Agents/Experimental/Arguments/TransformerKolmogorovScaling.agda` ties the
Kolmogorov/Kt discovery predicate directly to the transformer training bridge:

- `UniversalIRCompile` + `CodeBudget` define size + budget for codes via the
  UniversalIR backend (so complexity is comparable across implementations).
- `KtOptimalLoss` expresses optimality **relative to the training observable**
  (loss), matching actual transformer training semantics.
- `KolmogorovBridge` packages a transformer `TrainingSpec` with the loss
  observable and a stability assumption, yielding the same scaling bound as in
  the abstract discovery theory.
- `BudgetPhase` + `TwoRegimeBridge` express a **compute-budget phase boundary**
  and yield separate scaling bounds in the low/high regimes.
- `ComputeDataBudget` + `ChinchillaBridge` add a **data vs compute** regime
  split, and `chinchilla-compare` selects the appropriate scaling bound.
- `codeBudget-from-resources` / `computeDataBudget-from-resources` lift resource
  accounting into the Kolmogorov and Chinchilla bridges.

### Explicit exponents (multiplicative scale)

`LogOS/QAdapters/QNatMul.agda` supplies a specific multiplicative scale
(`QNatMul`): scale composition is `mul`, time is mapped by exponentiation (`exp₂`),
and `pow` makes the scaling exponent explicit at the quantale level.

This is a direct “theory → instantiation” link: the discovery predicate is
still self‑referentially publicisable, but its observable is the chosen loss
used by a transformer training instantiation.

### Relation to known results

The Maxwell-agent story sits inside a large body of "information thermodynamics"
results about feedback control, measurement, and irreversibility. The LogOS
statements are deliberately abstract, so they align with several known patterns:

- **Landauer/Bennett:** a lower bound on irreversible information loss per
  learning step, made parametric over any boundary IO model.
- **Maxwell demon with feedback (Sagawa-Ueda, etc.):** learning/measurement can
  enable work extraction, but the information gained is bounded and paid for
  through entropy production; in LogOS this appears as Landauer + capacity +
  DPI assumptions.
- **Information flow and learning-rate bounds:** data-processing constraints on
  post-processing of measurements are captured abstractly by `DPI.Channel` and
  `MeasurementCapacity`, yielding explicit condensation bounds.
- **Evaluation and universal simulators:** the "universal evaluator inherits the
  same cost bound" is a packaging of the standard universality story with
  Landauer, and is rarely stated explicitly in agent form.

The point is not to replace the physics literature, but to provide a **single
kernel-level envelope** that can be instantiated to mirror these results while
keeping assumptions fully visible.

### Bibliography pointers (not exhaustive)

- R. Landauer (1961), "Irreversibility and Heat Generation in the Computing Process".
- C. H. Bennett (1982), "The Thermodynamics of Computation - A Review".
- T. Sagawa and M. Ueda (2010), "Generalized Jarzynski Equality under Nonequilibrium Feedback Control".
- M. Esposito, K. Lindenberg, and C. Van den Broeck (2010), "Entropy Production as Correlation between System and Reservoir".
- U. Seifert (2012), "Stochastic Thermodynamics, Fluctuation Theorems and Molecular Machines".
- L. P. Kadanoff (1966), "Scaling Laws for Ising Models Near Tc".
- K. G. Wilson (1971), "Renormalization Group and Critical Phenomena. I. Renormalization Group and the Kadanoff Scaling Picture".

### Agents pack proof ledger (formal status)

This section is a proof-status map for the whole Agents pack. Each item is
tagged by its status: definition (syntactic), theorem (proved in Agda), or
assumption (a record field supplied externally).

Definitions (syntactic):

- `AgentSocket` and `Auditor`/`Monitor` interfaces.
- `Policy`, `Update`, `LearningStep`, `RGStep`, `RGStable`.
- `TrainingSpec`, `TransformerKernelBridge`, `ResourceBudgets`.

Theorems (proved in Agda):

- `μPolicy-unfold-left` and `μPolicy-induction` (learning fixed points, under the explicit
  boundary `OmegaCPO` hypothesis carried by `Learning.FixedPoint.For`).
- `rg-least-stable` (least RG-stable fixed point, under boundary `OmegaCPO`).
- `rg-μ-fixed` (μ is a fixed point, additionally assumes `ScottContinuous` for the RG update endomap).
- `scalingBound-from-stable` (scaling law from RG stability, in `ScalingLaws.For` with
  a graded kernel + boundary `OmegaCPO`).
- `learning-cost-lower-bound` (Landauer lower bound, assuming `LandauerIOAssumptions`).
- `learning-condensation-bound` (information condensation bound, assuming `MeasurementCapacity` + DPI).

Assumptions (explicit fields, not proven here):

- `Oracle` contents for auditors and any safety contract instantiations.
- Landauer, capacity, and DPI assumption packs (`LandauerIOAssumptions`,
  `MeasurementCapacity`, `DPI.Channel`).
- Any concrete transformer semantics used to instantiate `TrainingSpec`.

Interpretive alignments (informal, not used in proofs):

- Treating `AgentSocket` as a full RL agent or LLM pipeline.
- Interpreting `ResourceBudgets` as exact FLOP/token accounting.

### Cross-pack pointers

To situate the Maxwell-agent story in the broader library:

- Physics-of-information surfaces live in `LogOS/Packs/Complexity/Experimental/PhysicsOfInformation.agda`
  (experimental) and are explained in `docs/Library.lagda.md` and `docs/Applications/Complexity.lagda.md`.
- Universality machinery (shared processes, scheme equivalence) lives in
  `LogOS/Packs/Universality/Surface.agda`, and is the reason universal evaluation
  is treated uniformly across agent frameworks.
- Opacity boundaries (auditing and observability limits) live in
  `LogOS/Packs/Opacity/Experimental/Surface.agda` (experimental) and explain why learning
  evidence must be phrased at the boundary constraint level.

### Numerical stability (motivation, LogOS-native)

Several stability measures fall out naturally from the existing structure and
admit instantiations:

- **Grade-bounded updates:** in graded kernels, the step-grade or a chosen scale
  element can be read as a stability budget; `ClosureStepAt` composes by
  quantale multiplication, so the budget is tracked explicitly.
- **Flow-clipping analogy:** `id ≤ update ≤ Flow` gives a monotone envelope for
  updates; this can be read as analogous to clipping or proximal updates.
- **Information bottleneck:** use `MeasurementCapacity` and DPI to cap the
  classical information extracted per update; this yields a formal bound that is
  often read as limiting overfitting pressure.
- **Tensor blending:** combine learned policy with symbolic or safety constraints
  using `_⊗∂_`; this is a monotone merge operation built into the boundary
  algebra.
## UniversalIR reuse (framework instances)

Frameworks are defined minimally as a `Choice` into a shared `Process`
(`LogOS/Packs/Agents/Frameworks/Core.agda`). The concrete embeddings currently
supplied are the UniversalIR paradigms (closed on the `PATask` input):

- `LogOS/Packs/Agents/Frameworks/UniversalIR.agda` (curated surface via
  `LogOS/Packs/UniversalIR/Core.agda`), which exports `UProcess` plus
  `minskyChoice`, `lambdaChoice`, `ethereumChoice`, `oracleChoice`,
  and `quantumCircuitChoice`.
- `LogOS/Packs/Agents/Frameworks/PATask.agda` packages these as
  `Framework` instances (`minskyFramework`, `lambdaFramework`, ...) so they can be
  plugged into an `AgentSocket` without extra boilerplate.
- Budgeted variants (explicit step bounds) are also provided by the same module,
  using `Bounded PATask` as the task type (`boundedMinskyFramework`, ...).

Agreement between the UniversalIR frameworks is available in two flavours:

- Machine-scheme agreement: `LogOS/Packs/Agents/Frameworks/PATaskAgreement.agda`
  re-exports the paper-facing `ParadigmsRunEq` statement.
- Choice-scheme agreement: the same module provides `ChoiceSchemesRunEq` for
  the UniversalIR `Choice`-based schemes (the ones used by `Framework`).

Other “known framework” modules are **mostly interfaces or meta-theory surfaces**;
when they include translations into UniversalIR, they are intentionally minimal:

- `LogOS/Packs/Agents/Frameworks/AIXI_Bounded.agda` and
  `LogOS/Packs/Agents/Frameworks/OOPS.agda` expose the generic `SchemeCategory`
  machinery, and now include minimal **bounded PATask** translations into
  `UProcess` (`aixiChoice`/`oopsChoice`, with `aixiFramework`/`oopsFramework`).
  These are checked instantiations, not full RL or optimal‑search models.
- `LogOS/Packs/Agents/Frameworks/GodelMachine.agda` and
  `LogOS/Packs/Agents/Frameworks/MetaReasoning.agda` re-export meta-theory
  (Lob/Godel/no-omniscience) rather than a concrete process translation.

So, at present: **UniversalIR is the main provided, checked integration** of
agent-like task languages into a shared process (`UProcess`), with reusable
transport/agreement tooling. To integrate another framework into UniversalIR, supply
a `Choice` into `UProcess` (and, if needed, a `ProcessHom`
or a cost/budget-carrying `ProcessHomCost` / `ProcessHomCostWithGrade`, or the
corresponding `mapChoice`/`mapChoiceLax` transport), then plug it into an
`AgentSocket`.

## Kernel-native frameworks (tasks = code or boundary constraints)

If you want the agent story to be “as LogOS-native as possible”, the kernel can
be treated as the shared process directly:

- `LogOS/Packs/Agents/Frameworks/KernelNative.agda` provides `codeFramework` and
  `boundaryFramework` constructors for `LogicKernel`, `Kernel`, and `GradedKernel`.
- The task type becomes either `Code` (execute a code fragment for a chosen fuel)
  or `Con_bnd` (evolve a boundary constraint for a chosen fuel).

This yields a kernel-internal agent substrate within the formal model: tasks are
literally the objects of the kernel’s own computational process.
