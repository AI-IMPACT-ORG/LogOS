<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Observer Semantics (Physical Reading of LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.Views.ObserverSemantics where

-- Typechecked “view surface” for the observer-semantics reading.
--
-- Keep this module lightweight to avoid name clashes when imported alongside
-- other views/tests.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheorems
import LogOS.Boundary.Telemetry as Telemetry

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = ViewTheorems.For K
  open V.ObserverSemantics public

  private
    Entails∂-exists : _
    Entails∂-exists = Entails∂

    Entails∂-budget-exists : _
    Entails∂-budget-exists = Entails∂-budget

    BudgetedAdequacy-exists : _
    BudgetedAdequacy-exists = BudgetedAdequacy

    sound-complete∂-budget-exists : _
    sound-complete∂-budget-exists = sound-complete∂-budget

    boundaryIO-exists : _
    boundaryIO-exists = boundaryIO

    module _ (T : Telemetry.TelemetryTrace ℓ)
             (P : Telemetry.ProgramTelemetryPort Sig Q (Kernel.HWorld K)
                    (Kernel.BB K) (Kernel.HTruth K) boundaryIO T)
             where
      module TB = TelemetryBudget T P

      budget-from-trace-exists : _
      budget-from-trace-exists = TB.budget-from-trace

    Safe⋆-generic-exists : _
    Safe⋆-generic-exists = SafeReflection.Safe⋆-generic

    Safe⋆-kernel-exists : _
    Safe⋆-kernel-exists = SafeReflection.Safe⋆-kernel

    safe⋆-core-kernel-exists : _
    safe⋆-core-kernel-exists = SafeReflection.safe⋆-core-kernel

    safe⋆-sound-kernel-exists : _
    safe⋆-sound-kernel-exists = SafeReflection.safe⋆-sound-kernel

    safe⋆-mono-Truth-kernel-exists : _
    safe⋆-mono-Truth-kernel-exists = SafeReflection.safe⋆-mono-Truth-kernel

    projection-exists : _
    projection-exists = V.Projections.projection
```

Purpose
-------
This is a **non-canonical view** of the LogOS kernel: it is intentionally more
physical than the “classic logic” and “HoTT positioning” views.

The goal is to make explicit how LogOS naturally supports an **observer-centric**
semantics that shares minimal structural shape with:

- *Categorical quantum mechanics* (CQM): processes, monoidal-*ops* composition, and (optional) dagger structure,
- “physics as computation”: computation as physical process constrained by locality/causality/resources,
- “complexity as a physics statement”: what can be decided/observed under resource constraints.

This is a documentation view: it does **not** claim that the library derives the laws
of physics. Instead it shows where to *plug in* physically meaningful axioms/packs,
and what generic theorems LogOS then provides.

Interpretation (analogy):
this document is a derived presentation (“view”) over the same kernel interfaces;
it does not add logical power.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Notation (local)
----------------
- `c ⊑ d`: refinement/entailment in a preorder.
- `c ≈ d`: mutual refinement.
- `P ↔ Q`: satisfaction equivalence.
- `x ≡ y`: propositional equality (`_≡_`), not judgmental equality.

Scope (formal)
--------------
- Parameter: `Kernel Sig Q` (as used by `ViewTheorems.For`).
- Core observer layer: phrased for `LogicKernel Sig Q`, derived from any `Kernel Sig Q` via
  `LogOS/Kernel/LogicKernel/FromKernel.agda`.

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Observable/measurement outcome | boundary observation via `BoundaryIO` / ports | Presented as boundary satisfaction, not as a built-in probability calculus. |
| Observer | predicates on `Code` (and/or telemetry traces) | Observers can carry witnesses (traces/certificates), hence universe levels matter. |
| Coarse-graining / reindexing | `SigHom`, `reindexKernel`, port translations | Signature change and port/adapters both model “change of description”. |
| Resource/budget algebra | `QAdapter` (scale) and `BudgetedTier` / telemetry budgets | Resource predicates are explicit assumptions, not hidden global axioms. |
| Stabilised truth (closure) | guarded closure `Flow`, stable truth `Th*` | Stability is closure pre-fixedness (hence fixed up to `≈`), not judgmental equality. |

Core definitions (literature style)
-----------------------------------

**Definition (Observer predicate).** An observer is a predicate on code
(`Code → Set …`) equipped with two stability conditions:
- decode-extensionality (depends only on decoded meaning, up to decoded mutual refinement), and
- step-stability (invariant under the chosen code step).

**Definition (Largest admissible/observable fragment).** `Observable⋆ TruthK` is
the largest predicate (w.r.t. pointwise implication) that is decode-extensional,
step-stable, and sound into a target truth predicate `TruthK`. This is the core
construction of `ObserverCore` and is instantiated from any `LogicKernel` by
`ObserverFromLogicKernel`.

Assumptions (explicit)
----------------------
- This view is interpretive: any *physical* axioms (e.g. symmetry, dagger, probabilistic structure) must be added explicitly as packs; the kernel does not assume them.
- Completeness/adequacy claims are conditional (not global): budgeted adequacy is an explicit hypothesis.
- Budgets are predicates on observations/traces (e.g. from telemetry); LogOS does not assume a built-in cost model.

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: observer/coarse-graining ideas as explicit interface change (signature maps, port translations) and order-theoretic monotonicity statements.
- Weaker/lax by default: no probabilistic/dagger structure is assumed; “stability” is closure pre-fixedness (hence fixed up to `≈`), not judgmental equality.
- Added by ports/adapters: the observer boundary is a first-class semantic interface, and resource/budget indexing is supported by graded/budgeted variants without changing the core kernel.
- Assumption-scoped: any physical axioms and any (budgeted) adequacy/completeness are explicit hypotheses, not global claims.

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `ObserverSemantics`):
  `Entails∂`, `Entails∂-budget`, `BudgetedAdequacy`, `sound-complete∂-budget`, `boundaryIO`.
- Telemetry‑derived budget predicate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `ObserverSemantics.TelemetryBudget`),
  `budget-from-trace`.
- Safe reflection (generic + kernel-specific):
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `ObserverSemantics.SafeReflection`),
  `Safe⋆-generic`, `Safe⋆-kernel`, `safe⋆-core-kernel`,
  `safe⋆-sound-kernel`, `safe⋆-mono-Truth-kernel`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- The prose below is explanatory; the statements above are the authoritative claims.

Micro-example (two steps, same decoded behaviour)
-------------------------------------------------
The observer machinery is insensitive to the *presentation* of the code step,
as long as the decoded step agrees up to decoded mutual refinement.

In particular, for a `LogicKernel` the library relates:
- the raw operational step `FlowCode : Code → Code`, and
- the “compute then stabilise” step `BoxAt step (Body _)`,

via a decode-level equality and then a packaged transport lemma for observer
predicates (`StepTransport≈` / `Pred⋆≈-cong-step` in `ObserverCore`).

Pointers (no repetition)
------------------------
- Kernel/tier bookkeeping: `docs/LogOS_Core_Spec.lagda.md`.
- CHL-facing step story (`RawStep` vs `Step`): `docs/Views/CurryHowardLambek.lagda.md`.
- Ports/adapters backbone (presentation transport): `docs/DeepDive/Architecture_PortsAdapters.lagda.md`.

Extended discussion (optional)
-----------------------------
The remainder develops a richer “physics-of-information” narrative and points to
downstream packs. The authoritative claims are the theorem surfaces cited above.

Signature maps as coarse-graining (optional)
--------------------------------------------
In many physical readings, changing the “interface signature” corresponds to renaming observables
or forgetting measurement structure (a coarse-graining). LogOS supports this in two complementary
directions:

- **Models (contravariant):** pull back kernels along signature maps via `reindexKernel` / `reindexLogicKernel`.
- **Programs/sentences (covariant, optional):** translate a signature-indexed constraint/program language along
  `SigHom` via `LogOS/Free/ConstraintsOverSig.agda` (`rename∂`).
- **Strict syntax (optional):** `reindexKernelWithFml` / `reindexLogicKernelWithFml` add a sentence translation layer
  for strict formulas (keeps constraints + code fixed).

## 1) The central move: replace “truth” by “what an observer can stably communicate”

The Kernel does not assume a single global truth predicate. Instead, it provides:

- an H-tier satisfaction `Sat_H w c` (“local truth in a world/context”), and
- a G-tier closure step `Flow` on boundary constraints,
  with a distinguished lax fixed-point witness `Th*`.

Interpretation (analogy):

- **constraints** are propositions about a system-at-a-boundary,
- **observation/interaction** is represented as *admissible steps* that transform constraints,
- **stability** is what remains invariant under the global “communication/regularization” step `Flow`.

This matches a common physics posture:

> a proposition is only “physically meaningful” insofar as it is stable under a specified
> observation/communication regime.

In the library, this is one reason fixed-point structure is kept in preorder form: it’s
an *observational* notion by default, and equality is an optional upgrade.

Canonical instance (code)
-------------------------
The generic observer-semantics core (`LogOS/Theorems/Meta/ObserverCore.agda`) can be instantiated
uniformly from any CHL-facing `LogicKernel`, using the kernel’s own `FlowCode` step:

- `LogOS/Theorems/Meta/ObserverFromLogicKernel.agda`

Minimal vocabulary (formal)
---------------------------
The following terms are used as names for concrete interfaces in this view. They
do not, by themselves, assert a physics interpretation; that interpretation only
comes from the chosen model/axioms.

- **System**: a `Kernel Sig Q`, or (when using the observer-core theorems directly) its derived `LogicKernel Sig Q` (write it as `K`).
- **State of knowledge at the boundary**: a boundary constraint `c : Con` in the boundary preorder.
- **Decoded meaning of code**: `decode : Code → Con` from the kernel.
- **Observer step / admissible interaction**: the derived operational step on code
  `BoxAt (GTier.step (LogicKernel.G K)) (Body _) : Code → Code` (“compute-then-stabilise at the step grade”).
  In a `LogicKernel`, this is equal after decoding (≡) to the raw operational step
  `FlowCode : Code → Code` (defined as `Guard ∘ Body`); see
  `ObserverFromLogicKernel.For.decode-stepFlowCode≡decode-step` and the induced
  predicate equivalence (↔) `ObserverFromLogicKernel.For.Observable⋆↔Observable⋆-FlowCode`.
- **Stabilisation / “what survives communication”**: the kernel-derived closure modality on code.
  In graded form: `BoxAt g γ := encode (Flow g (decode γ))`. `Box` is the ungraded/saturation instance.
  (`LogOS/Kernel.agda`, `LogOS/Kernel/Graded.agda`, `LogOS/Kernel/LogicKernel.agda`).
- **Step invariance (decode-level)**: `ObserverCore.Pred⋆≈` only depends on the step up to decoded mutual refinement (`≈`).
  If `decode (step γ) ≈ decode (step′ γ)` for all `γ`, then `Pred⋆≈` for `step` and `step′` are predicate-equivalent (↔)
  (`ObserverCore.Pred⋆≈-cong-step` in `LogOS/Theorems/Meta/ObserverCore.agda`).
  (Legacy, ≡-based: `ObserverCore.Pred⋆-cong-step`.)
- **Step transport (packaged)**: the same hypothesis also transports *stability* and *admissibility* for
  decode-extensional predicates, via `ObserverCore.StepTransport≈` (it bundles `stableUnder`, `admissible`, and `Pred⋆≈↔`).
  (Legacy, ≡-based: `ObserverCore.StepTransport`.)
- **Truth predicate** (choice): any `TruthK : Code → Set` (e.g. “true at world w” below).
- **Observable / communicable fragment** (canonical from a `TruthK`): the *largest admissible* predicate
  `Observable⋆ TruthK` (largest w.r.t. `_≤Pred_` (pointwise implication) among predicates that are decode‑extensional,
  step‑stable, and sound into `TruthK`), obtained by the generic
  `ObserverCore.Pred⋆` construction (see `ObserverCore.Pred⋆-admissible` and `ObserverCore.Pred⋆-largest`),
  instantiated via `ObserverFromLogicKernel.For.Observable⋆`.
- **Universe-level tradeoff** (important for pack APIs): `Pred⋆`/`Observable⋆` is defined as a `Σ` over observer
  predicates `P : Code → Set ℓP`, so it necessarily lives one universe higher (in `Set … ⊔ lsuc ℓP`).
  Instantiating at `ℓP = lsuc ℓ` allows witness-carrying observers (e.g. traces/certificates), but yields
  pack-level predicates like `Code → Set (lsuc (lsuc ℓ))`. Instantiating at `ℓP = ℓ` tightens the types, but
  restricts observers to propositional ones (no large witnesses).
- **Truth at a world** (canonical example of a `TruthK`): `TruthAt w γ := Sat_H_bnd (to∂ w) (decode γ)`
  (see `ObserverFromLogicKernel.For.TruthAt`).
- **Guarded truth at a world** (canonical “stable fragment” of `TruthAt`): the largest admissible,
  decode‑extensional, step‑stable predicate contained in `TruthAt w`, packaged as
  `LogOS/Theorems/Meta/GuardedTruthAt.agda`. This can be presented using either
  “compute-then-stabilise” or `FlowCode`; see
  `GuardedTruthAt.For.GuardedTruthAt↔GuardedTruthAt-FlowCode`.
- **Refinement preserves truth** (alignment with the 2-category): if `f ⇒ g` as 2-cells of kernel morphisms,
  then `TruthAt w (mapCode f γ) → TruthAt w (mapCode g γ)` (see
  `ObserverFromLogicKernel.RefinementPreservesTruthAt` and `Meta/RefinementSoundness`).
- **Port/adapters calculus** (boundary-level 2-category): boundary ports are objects, adapters are 1-cells,
  and adapter equivalence `Adapter≈` (defined pointwise by satisfaction equivalence (↔)) is the 2-cell notion
  (`LogOS/Theorems/CategoryTheory/Port2Cat.agda`).

```agda
  -- Anchor: `TruthAt` expands to `Sat_H_bnd (to∂ w) (decode γ)` by unfolding the definition (proof is `refl`).
open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Kernel.LogicKernel as LK
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObsLK

private
  module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : LK.LogicKernel Sig Q) where
    module O = ObsLK.For {Sig = Sig} {Q = Q} K
    TruthAt-explicit
      : ∀ (w : LogOSSignature.Cosp Sig) (γ : LK.LogicKernel.Code K)
      → O.TruthAt w γ ≡ LK.LogicKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (LK.LogicKernel.decode K γ)
    TruthAt-explicit _ _ = refl
```

## 2) Observers as processes: the Endo DSL and tensor

LogOS exposes a conservative process DSL on boundary constraints:

- `LogOS/Kernel/Endo.agda` packages monotone endomaps (`Endo K`) and their refinement order (`_≤₂_`).
- `LogOS/Kernel/TensorEndo.agda` provides canonical “tensor/whiskering” endomaps and laws that make
  process composition ergonomic.
- `LogOS/Kernel/TensorDSL.agda` re-exports the above as the recommended surface.
- `LogOS/Kernel/Graded/Endo.agda` mirrors the DSL for graded kernels (grade‑indexed steps with
  `_∘StepAt_`/`_thenStepAt_`), and `LogOS/Kernel/Graded/All.agda` re‑exports the graded surface.

Physical reading:

- an **observer** is a process that maps “what is asserted at the boundary” to an updated boundary assertion,
- composition is sequential interaction,
- tensor/whiskering is a monoidal “side-by-side” composition in the *ops-first* sense:
  a tensor/unit operation with monotonicity. Associativity/unit laws (and braiding/symmetry)
  are optional and live in explicit law packs when you want textbook monoidal laws.
  This can be read as independence/parallelism once a model interprets the tensor that way.

Crucially, the process calculus is **ordered**: endomaps are compared by pointwise refinement (`_≤₂_`),
so “being at least as informative / at least as strong” is part of the structure, not a derived notion.
This is the same order that appears as 2-cells in the kernel refinement 2-category:

- `LogOS/Kernel/LogicKernel/Hom2Cat.agda`
- `LogOS/Theorems/CategoryTheory/WrapperCore.agda`
- `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda` (refinement 2‑category interface)
- `LogOS/Theorems/CategoryTheory/Kernel2CatGraded.agda` (refinement 2‑category interface)

This matches a common minimal starting shape for CQM: a monoidal-*ops* setting of processes with
parallel and sequential composition, where “systems” are the objects and “processes”
are the morphisms. Symmetry/braiding (and other coherence laws) is optional and
lives in explicit algebra packs.

LogOS differs in emphasis: it does not start by postulating a dagger compact category;
it starts by postulating only what the kernel needs (preorders + laxness), and then
lets richer structure be added as explicit packs.

## 3) Non-unitarity and measurement as counted “global events”

A typical physics/quantum split is:

- unitary/local evolution (reversible, information-preserving), vs
- measurement / forgetting / coarse-graining (non-unitary, information-destroying or gaining).

LogOS already has a natural landing pad for this split:

- `LogOS/Domain/Complexity/MeasurementCapacity.agda` (records `MeasurementCapacity`,
  `NonUnitaryCapacity`, with optional non-vacuity guards),
- `LogOS/Domain/Complexity/DataProcessingInequality.agda` (DPI interface/axiom pack: channels + an information measure monotone under post-processing),
- `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda` (bundle time + non-unitary + information capacities).

Interpretation (analogy):

- “local unitary evolution” lives in the **choice of computation surface** (e.g. circuit stepper),
- “measurement/forgetting” is modeled by a **budgeted global capability** (a separate resource axis),
- “what an observer can conclude” is a theorem of the form:
  *given a budget, no decider/oracle of a certain strength exists*.

This reframes many “no-go” arguments (diagonal/Rice/Tarski style) as **observer-limited**
statements: a fully total oracle would exceed the allowed physical/observational regime.

Quantitative note: in the production kernel, “resource” lives in the adapter `QAdapter` as a
unital quantale in the finite-join sense (not complete) `Scale`. Sequential composition is modeled by quantale
multiplication (`_·_`), alternative allowances by join (`_⊔s_`), and `⊥s` is the minimal budget.
UniversalIR’s default cost model (`QNat2`) is a two-axis quantale (unitary work vs measurement
events; see `LogOS/QAdapters/QNat2.agda`), making “measurement has a counted cost” a first-class notion.

## 4) CQM alignment: what is already present vs what is an extension

What is already structurally present in the production library:

- **Monoidal-*ops* process shape**: sequential composition + tensor/whiskering at the boundary (`TensorEndo` view).
- **Dagger-shaped hooks**: there is a dedicated meta development around dagger-like structure and positivity
  used by spectral/opacity packs (see `LogOS/Theorems/Meta/Dagger.agda` and related ledgers).
- **Explicit circuit syntax**: UniversalIR includes an explicit circuit language and examples:
  `LogOS/Domain/UniversalIR/Core/QuantumCircuit.agda` and `LogOS/Domain/UniversalIR/Examples/QuantumCircuit.agda`.

What is intentionally *not* built into the kernel (and would be an “extension pack”):

- a full **dagger compact** structure with cups/caps and yanking laws,
- a chosen **CPM/CP\* construction** for mixed-state/observable semantics,
- locality/causality axioms (e.g. a factorisation/screening-off law) as default assumptions.

This separation is a design choice: the kernel stays host-minimal and model-agnostic;
physics-aligned structure is opt-in and explicit.

## 5) A concrete “observer semantics pack” (minimal assumptions)

The minimal upgrade that makes the physics story explicit (without changing the kernel) is:

1. **System/process interface** (CQM-shaped):
   - choose a category of “systems” (objects) and “processes” (morphisms),
   - equip it with monoidal tensor and identities/composition (often already implicit in your model).

2. **Observer interface**:
   - a distinguished class of “observations” (effects/tests) and their composition laws,
   - an “observability” predicate: when is a proposition/test in the observable sector?

3. **Locality/causality/local unitarity axioms** (scoped):
   - locality: compositional factorisation laws for independent subsystems,
   - causality: discarding/termination behaves functorially (no-signalling style constraints),
   - local unitarity: a reversible sublanguage/process class, separated from global non-unitary events.

4. **Resource bridge**:
   - connect observer operations to `ObservabilityBudgetGraded` (time + non-unitary + information),
   - use existing complexity bridges to turn those axioms into “no total oracle / no poly decider” theorems.

This pack would be “less canonical” because it chooses a *physics interpretation* of
what the kernel primitives mean; but it is extremely aligned with how the repo already
structures computation and physical constraints.

## 6) What it buys you immediately (without major refactors)

- A single place where the “physics vocabulary” is defined (observer, locality, causality, unitary vs non-unitary),
  instead of being spread across multiple complexity/universality modules.
- Cleaner statements of “physical bottleneck ⇒ separation” theorems as **observer-limited** claims:
  what cannot be observed/decided under the allowed regime.
- A clearer bridge to CQM and computational-physics narratives:
  computations are processes; observers are restricted process families; impossibility theorems are resource bounds.

Connections (where to connect)
------------------------------
- Kernel closure/reflection: `LogOS/Kernel.agda`
- Endomap/tensor DSL: `LogOS/Kernel/TensorDSL.agda`
- Physical budgets: `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda`
- Non-unitary/info axioms: `LogOS/Domain/Complexity/MeasurementCapacity.agda` (records `MeasurementCapacity`,
  `NonUnitaryCapacity`, plus optional non-vacuity guards),
  `LogOS/Domain/Complexity/DataProcessingInequality.agda`
- Complexity physical story: `docs/Applications/Complexity.lagda.md`
- Circuit surface: `LogOS/Domain/UniversalIR/Core/QuantumCircuit.agda`

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`
- Meredith sentences (LogicKernel / CHL core): `docs/Views/MeredithSentences.lagda.md`
- Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
- Topos-shaped nuclei/sheaves reading: `docs/Views/Topos.lagda.md`
