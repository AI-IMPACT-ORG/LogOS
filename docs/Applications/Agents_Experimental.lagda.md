<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Agents (Experimental Extensions) (LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.Agents_Experimental where

-- Note: we avoid importing the full experimental surface lock here, because it
-- forces typechecking of the entire experimental pack (slow for docs builds).
-- Path references in prose are checked by `doc-reference-check`, and the
-- typechecked anchors below import only the modules this document depends on.

open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary ; ConPreorder)
open import LogOS.Minimal.Truth as Truth
open import LogOS.API.Kernel using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization as TransformerFormalization
import LogOS.Packs.Agents.Experimental.Arguments.DiscoveryScaling as DiscoveryScaling
import LogOS.Packs.Agents.Experimental.Arguments.DocsAnchors as DocsAnchors
import LogOS.API.Kernel.Graded.Endo as GEndo

-- Docs anchor aliases (typechecked).
module ControlledFeedbackAlignment = DocsAnchors.ControlledFeedbackAlignment
module LogOSTriggerAlignment = DocsAnchors.LogOSTriggerAlignment

```

This note documents the **experimental extensions** of the Agents storyline.
For the stable surface (socket + monitoring/auditing + learning + frameworks),
see `docs/Applications/Agents.lagda.md`.

Trust level:
- **experimental** (lock surface: `LogOS/Packs/Agents/Experimental/Surface.agda`;
  umbrella: `LogOS/Packs/Agents/Experimental/All.agda`)

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Interpretation (analogy)
------------------------
Interpretation (analogy): this note uses vocabulary such as “RG”,
“Maxwell-agent-style”, and “transformer scaling” as interpretation. The literal content is
always the referenced Agda definitions/theorems and their explicit hypothesis
records; no empirical claim follows without an explicit model/instantiation.

## Physics of information (Maxwell-agent-style view) — experimental

This section depends on the complexity/physics pack and is available only via
`LogOS.Packs.Agents.Experimental.All` (`Experimental.Physics.*`).

The Agents pack can be treated as a **laboratory** where learning is constrained
by physics-of-information primitives rather than pure CS cost models:

- `LogOS/Packs/Agents/Experimental/Physics/All.agda` re-exports the experimental physics surfaces
  (`PhysicsOfInformation`, `MeasurementCapacity`, `DataProcessingInequality`,
  `InfoProcessingBounds`).
- `LogOS/Packs/Agents/Experimental/Physics/MaxwellAgent.agda` packages a socket together with
  a Landauer-style cost lower bound and a measurement-capacity bound.

Under these assumption packs, one can read a "Maxwell-agent-style" story
(formal analogy inside the supplied cost/capacity interface): learning and
policy updates are allowed, and irreversibility/classicalization are bounded by
the supplied Landauer and capacity parameters.

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
DSL. This is the most kernel-native encoding: grades live in the prequantale scale,
and RG composition multiplies grades (the explicit monoid/prequantale structure of `Scale` in `QAdapter`).

The new RG surface lives in `LogOS/Packs/Agents/Experimental/Learning/RGFlow.agda` and gives:

- `RGStep g = ClosureStepAt K g`: RG updates are closure steps at grade `g`.
- `rg-compose` + `rg-promote`: RG morphisms compose by grade multiplication and
  can be promoted along the prequantale order (lax enrichment).
- `rg-μ`, `rg-unfold-left`: Kleene μ RG policy + unfold-left inequality (`rg-μ s ⊑ applyRG s (rg-μ s)`).
- `rg-unfold-right`: unfold-right inequality (`applyRG s (rg-μ s) ⊑ rg-μ s`), additionally assumes
  `ScottContinuous` for the update endomap (`RGFlow.rg-unfold-right`).
- `rg-least-stable`: **classification result** — the Kleene μ policy `rg-μ` is the least
  RG-stable (pre-fixed) policy.
- `RGLyapunov` + `rg-lyapunov-iter`: prequantale-valued Lyapunov potentials give a
  monotone “energy/complexity” descent for RG iterations.
- `CFunction` / `AFunction`: CFT-aligned analogs; values live in `Time` and are
  compared via `τ : Time → Scale`, so additivity under `_+_` corresponds to
  multiplicative budgets in the prequantale. `AFunction` is additionally
  lax-monoidal under the boundary tensor.
- `LogOS/Packs/Agents/Experimental/Learning/RGFlow/Info.agda` (optional import):
  information-theoretic refinements (`InfoCFunction`, `InfoAFunction`,
  `InfoToTime`) using measurement-capacity + DPI; `InfoToTime` lifts ℕ-valued
  information to `Time` so the c/a analogs inherit the same monotonicity
  statements.
- `RGTimeFlow`: a time-indexed RG flow (via `Time` and `τ-+`), with
  `CFunctionTime` / `AFunctionTime` giving time-indexed monotonicity, and
  `CFixedPointNormalization` / `AFixedPointNormalization` encoding central-charge
  normalization at RG fixed points.
- `RGTimeFlowLike` / `RGTimeFlowLax`: weaker time-indexed step interfaces when
  only the step (or one-sided composition) is available.
- `c-theorem-iter`, `c-theorem-fixed`, `a-theorem-iter`, `a-theorem-fixed`
  (c/a-theorem analogs): formal monotonicity, plus μ‑minimality results: the
  μ policy `rg-μ` is least among
  RG‑stable policies, hence minimises these observables among pre‑fixed points.
- `rg-learning-cost`: RG steps are soft updates, so Landauer bounds apply
  directly (physics-aware optimization).

This frames “RG stability” as a **learning-style optimization principle** inside
LogOS: stability is expressed as closure, composition is quantified by the
prequantale, and fixed points are computed via μ.

### Scaling-law argument (reflection closed) — experimental

This section documents the experimental scaling/transformer arguments. These
modules are *not* part of the stable Agents surface; import them via
`LogOS.Packs.Agents.Experimental.All` (`Experimental.Arguments.*`) if needed.

The formal scaling-law spine is packaged in
`LogOS/Packs/Agents/Experimental/Arguments/ScalingLaws.agda`:

- `obs-μ≤stable`: least RG-stable policies minimise observables
  (phase-transition interpretation anchor).
- `ScalingBound` + `scalingBound-from-stable`: code-level policies above the
  μ-policy `rg-μ` inherit the bound.
- `scalingBound-reify`: reflection closure (reify is observationally inert).
- `Public` submodule: if `step-grade = sat`, the bound is publicised via
  `LimitPublicisation`, and `scalingBound-public-reify` shows reify-invariance
  of the public predicate.

This makes the scaling-law story explicit within the stated assumptions: RG fixed
points supply the phase structure, scaling dimensions supply the exponents, and
reflection lemmas (e.g. `scalingBound-reify`) show invariance under internal
self-description (no extra meta-axioms).

### Transformer training (formalized assumptions) — experimental

`LogOS/Packs/Agents/Experimental/Arguments/Transformer.agda` is now a
lightweight marker module (kept for path stability). For theorem imports, use
the explicit modules listed below (`TransformerBridge`,
`TransformerFormalization`, `TransformerScalingPipeline`, etc.).

`LogOS/Packs/Agents/Experimental/Arguments/TransformerScaling.agda` turns the abstract RG
argument into a **transformer-specific** interface. Everything here is
*relativised*: `TransformerTraining` is an explicit hypothesis record, and the
consequences are theorems conditional on those fields (not empirical claims).

- `TransformerTraining` (hypotheses): a predicate on codes (`IsTransformer`),
  plus an RG step and scaling dimension for the training update.
- `transformer-scalingBound`: any RG-stable transformer policy obeys the scaling
  bound (theorem in the LogOS formal system, conditional on the
  `TransformerTraining` hypothesis record).
- `transformer-scaling-iter`: the iterate scaling law holds for the training RG
  step (theorem in the LogOS formal system, conditional on the
  `TransformerTraining` hypothesis record).
- `transformer-scalingBound-reify`: the bound is invariant under `reify`
  (reflection closure; theorem in the LogOS formal system, conditional on the
  `TransformerTraining` hypothesis record).
- `Public`: when `step-grade = sat`, the bound can be publicised via `Pr` using
  an explicit FlowCode-stability witness (theorem in the LogOS formal system,
  conditional on the `TransformerTraining` hypothesis record and that witness).

This is as tight as the stated assumptions allow without adding
transformer-specific axioms: the remaining work is to **instantiate** the RG
step and scaling dimension for a specific transformer training semantics, which
the library does not provide.
See “Pipeline proof ledger” and “Scaling literature alignment” below for a
line-by-line separation of definitions/theorems/assumptions and informal
interpretations.

Control-theory vocabulary for the kernel-side feedback discipline (`Flow`,
budgeted stabilisation, `BoxAt`/`Box`): `docs/Views/ControlledFeedback.lagda.md`.

“Naturalness” note (scope discipline):
- The controlled-feedback alignment is **literal** for training dynamics here:
  RG/training steps are defined as budgeted closure steps, and they ship with a
  proof they stay within `Flow` at that budget.
- It is *not* an identification of the attention forward architecture with the
  kernel’s `Flow`. A forward block is an endomap on representations; turning it
  into a `Flow`-style stabiliser would require choosing an information preorder
  on representations and proving the closure laws in that order.

Status note (incompleteness, explicit):
the transformer scaling story in this repository is a **conditional theorem
pipeline**, not a finished end-to-end derivation from “standard transformers +
SGD + cross-entropy” as deployed in practice.

Concretely, the pipeline is complete *as a template* (once you supply the
explicit `PipelineAssumptions` fields), but incomplete as an instantiation:
the library does not currently ship a concrete semantics that proves, for a
real training procedure, the key assumptions such as:

- `lossMonotone` and `lossOrder` (loss decreases and loss order reflects policy order),
- `trainingDiscover` / `discoveryCover` (discovery predicate covers trained parameter codes),
- the choice of `ResourceBudgets` and its connection to the intended “compute/data” regime split.

Completion checklist (what would make it “end-to-end” for a concrete model):
- Pick a concrete instantiation of `ControlledFeedbackCore` and `LossData`
  (a specific parameterization, observer, dataset, and loss). A transformer
  `forward`/`TransformerOps` package is one optional instance.
- Provide a `TrainingSpec g` (or equivalent) that pins down the RG training step
  and connects `trainParam` to the boundary update (`train-correct`).
- Discharge the stability gap either by:
  - proving the `lossMonotone`/`lossOrder` fields for your model, or
  - supplying RG stability directly (bypassing loss-order reflection),
    if you have an independent convergence/stability argument.
- Connect params/tokens/compute to a `ResourceBudgets` choice and justify the
  regime split you want to interpret (two-regime, Chinchilla-style, etc.).
- Make the discovery predicate operational (what is being “discovered”) and
  prove coverage (`trainingDiscover`/`discoveryCover`) for your instantiation.

### Controlled feedback core (kernel-native) — experimental

`LogOS/Packs/Agents/Experimental/Arguments/ControlledFeedback.agda` provides the
minimal LogOS-native training/scaling core:

- `ControlledFeedbackCore`: parameter space + policy encoding +
  controlled-policy predicate.
- `ControlledDynamics`: an RG step + scaling dimension, plus a parameter update
  consistent with the boundary update (`train-correct`).
- `IsTrainedStable`: trained controlled systems as RG-stable policies.
- `ConvergesToMu`: a Scott-continuity route to the canonical Kleene μ object
  (and hence the unfold-right inequality).
- `trained-scalingBound` and `trainedMu-scalingBound`: scaling-law consequences
  derived directly from the kernel (via RGFlow + ScalingLaws).

`LogOS/Packs/Agents/Experimental/Arguments/TransformerFormalization.agda`
remains as a compatibility layer: it keeps transformer-facing names
(`TransformerCore`, `TrainingDynamics`) but delegates semantics to the
controlled-feedback core.

This keeps architecture-specific detail explicit without hard-coding a
particular numerical semantics; the only assumptions are explicit record
fields, and any claim about a specific training procedure requires
instantiating those fields.

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

This is now explicitly the architecture-instance layer: theorem-critical
semantics live in `ControlledFeedback`, while transformer internals remain an
optional structure layer.

### Transformer scaling pipeline (end-to-end) — experimental

`LogOS/Packs/Agents/Experimental/Arguments/TransformerScalingPipeline.agda` refactors the
proof flow into a **single LogOS-native pipeline**. It is intentionally
explicit about which parts are definitions, theorems, and assumptions (see the
ledger below).

CI/runtime note (2026-02-09 profile):
- `make check-all` is the CI gate and always runs as a cold full check.
- `make check-quick` is the development loop: policy + full `*.agda` +
  library smoke (skips docs).
- `make check-quick-no-transformer` is the warm non-transformer loop: it skips
  the dedicated transformer pipeline pass (`PIPELINE_SKIP=1`).
- `scripts/check_all_agda.sh` now reports pass/module timings so the critical
  path is visible in logs.
- Measured runtime split:
  - warm `make check-quick`: main `~18s`, pipeline `~35-49s`
  - cold `make check-all`: main `314s`, pipeline `2765s`
- Dominant cold hotspots: `TransformerKolmogorovScaling` (`867s`),
  `TransformerScalingPipeline.Calibration` (`336s`),
  `TransformerScalingPipeline.ExperimentalCompute` (`277s`),
  `TransformerScalingPipeline.Examples` (`266s`),
  `TransformerScalingPipeline.Core` (`206s`), `EmitBridge` (`196s`).
- Interpretation: the short warm main-pass timing is expected cache behavior;
  the pipeline pass remains mandatory and carries most cost.

- `LossDynamics`: a loss‑as‑Lyapunov assumption yields RG stability and a
  scaling bound (purely kernel‑level, no transformer specifics).
- `nextTokenLossDynamics` specializes the loss dynamics to next‑token
  cross‑entropy observables.
- `PipelineAssumptions`: the minimal named inputs (`lossMonotone`, `lossOrder`
  (order‑reflecting), `resources`, `discover`, `trainingDiscover`,
  `discoveryCover`) that must be supplied
  to run the end‑to‑end theorem; `ComputeBudget` is derived from `resources`.
- `Pipeline`: connects transformer training (`OptimizerTraining`) to an
  explicit discovery predicate (`Discover`) and produces scaling bounds for
  discovered codes.
- `scalingRegimes-summary` + `scalingRegimes-theorem` package the summary in a
  single statement for the AI‑focused reader.
- `ResourceBudgets` + local `ComputeDataBudget` splitting lift
  **params/tokens/compute** into explicit compute/data regime comparisons.
- `policyCover` + `ChinchillaCorollary` restate the core claims in ML terms:
  discovered codes correspond to trained parameters, and compute/data regimes
  yield distinct scaling bounds.
- `training-causes-scaling` formalizes the conditional: if the discovery
  predicate holds for trained parameters, then the corresponding scaling bound
  follows.
- Implementation note: stability transport inside
  `LogOS/Packs/Agents/Experimental/Arguments/TransformerScalingPipeline/Core.agda`
  is taken from `ControlledFeedback`; transformer specifics stay behind bridge
  records.
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

`LogOS/Packs/Agents/Experimental/Arguments/DiscoveryScaling.agda` formalizes the claim
that a *discovery predicate* can force phase-transition and scaling structure.
Interpreting this predicate as “LogOS structure discovered during training” is a
separate hypothesis about concrete training dynamics (not a theorem of the
library).

- `DiscoveryAssumptions`: a downward‑closed predicate on policies (“LogOS
  structure discovered”), RG‑stability, and a scaling dimension (order
  parameter).
- `discovery-root`: any discovered stable policy forces discovery at the least
  RG fixed point `rg-μ` (phase-transition interpretation anchor).
- `PhaseTransition` + `transition-root`: if discovery ever becomes true, it is
  already true at `rg-μ`.
- `discovery-scalingBound`: discovered codes obey the scaling bound.

Formally: under `DiscoveryAssumptions`, discovery has a canonical “root” at the
least RG‑stable fixed point `rg-μ`, and discovered codes inherit scaling bounds.
Externally: whether empirical transformer training satisfies the assumptions is
an empirical/modeling question.

Typechecked anchor:
this document restates the trigger as `LogOSTriggerAlignment.trigger-at-μ` and
`LogOSTriggerAlignment.trigger-scalingBound` (see the top Agda block), so the
“LogOS-as-trigger” claim is pinned to concrete exported lemma names.

Historical note:
earlier revisions used the module name
`LogOS.Packs.Agents.Experimental.Arguments.LogOSDiscoveryScaling`.
The canonical source file is now
`LogOS/Packs/Agents/Experimental/Arguments/DiscoveryScaling.agda`.

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
Kolmogorov/Kt scaling structure to the transformer training bridge:

- `UniversalIRCompile` + `CodeBudget` define decode‑extensional size + budget
  for codes (implementation-agnostic, so complexity remains representation-safe).
- `KtOptimalLoss` expresses optimality **relative to the training observable**
  (loss), matching actual transformer training semantics.
- `Obs.ResidualBoundary` introduces a residual map `ρ : Dec → Resid`.
- `Obs.DiscoverCode` is now a lift of a residual predicate:
  discovery depends on `ρ (decode γ)`, not on full representation internals.
- `Obs.discover-residual` gives **partial representation independence**:
  equal residual boundary implies equal discovery status.
- `KolmogorovBridge` now carries a `discovery : Obs.ResidualDiscovery ...`
  witness (residual map + residual predicate + reify invariance).
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
and `pow` makes the scaling exponent explicit at the prequantale level.

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
- `rg-least-stable` (least RG-stable policy via Kleene μ, under boundary `OmegaCPO`).
- `rg-μ-fixed` (μ is fixed up to refinement, additionally assumes `ScottContinuous` for the RG update endomap).
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
- Universality machinery (shared processes, scheme equivalence `Sch.RunEq`) lives in
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
  prequantale multiplication, so the budget is tracked explicitly.
- **Flow-clipping analogy:** `id ≤ update ≤ Flow` gives a monotone envelope for
  updates; this can be read as analogous to clipping or proximal updates.
- **Information bottleneck:** use `MeasurementCapacity` and DPI to cap the
  classical information extracted per update; this yields a formal bound that is
  often read as limiting overfitting pressure.
- **Tensor blending:** combine learned policy with symbolic or safety constraints
  using `_⊗∂_`; this is a monotone merge operation built into the boundary
  algebra.
