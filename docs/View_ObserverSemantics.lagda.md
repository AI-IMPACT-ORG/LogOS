<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Observer Semantics (Physical Reading of LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.View_ObserverSemantics where

open import LogOS.Docs.Views.View_ObserverSemantics public
```

This note is a **non-canonical view** of the LogOS kernel: it is intentionally more
physical than the “classic logic” and “HoTT positioning” views.

The goal is to make explicit how LogOS naturally supports an **observer-centric**
semantics that aligns with:

- *Categorical quantum mechanics* (CQM): processes, monoidal composition, and (optional) dagger structure,
- Deutsch-style “physics as computation”: computation as physical process constrained by locality/causality/resources,
- Aaronson-style “complexity as a physics statement”: what can be decided/observed under resource constraints.

This is a documentation view: it does **not** claim that the library derives the laws
of physics. Instead it shows where to *plug in* physically meaningful axioms/packs,
and what generic theorems LogOS then provides.

Signature maps as coarse-graining (optional)
--------------------------------------------
In many physical readings, changing the “interface signature” corresponds to renaming observables
or forgetting measurement structure (a coarse-graining). LogOS supports this in two complementary
directions:

- **Models (contravariant):** pull back kernels along signature maps via `reindexKernel` / `reindexLogicKernel`.
- **Programs/sentences (covariant, optional):** translate a signature-indexed constraint/program language along
  `SigHom` via `LogOS/Free/ConstraintsOverSig.agda` (`rename∂`).

## 1) The central move: replace “truth” by “what an observer can stably communicate”

The Kernel does not assume a single global truth predicate. Instead, it provides:

- an H-tier satisfaction `Sat_H` (“local truth in a world/context”), and
- a G-tier closure step `Flow` on boundary constraints,
  with a distinguished (preorder) fixed point `Th*`.

Physical reading:

- **constraints** are propositions about a system-at-a-boundary,
- **observation/interaction** is represented as *admissible steps* that transform constraints,
- **stability** is what remains invariant under the global “communication/regularization” step `Flow`.

This matches a common physics posture:

> a proposition is only “physically meaningful” insofar as it is stable under a specified
> observation/communication regime.

In the library, this is exactly why fixed-point structure is kept in preorder form: it’s
an *observational* notion by default, and equality is an optional upgrade.

Canonical instance (code)
-------------------------
The generic observer-semantics core (`LogOS/Theorems/Meta/ObserverCore.agda`) can be instantiated
uniformly from any CHL-facing `LogicKernel`, using the kernel’s own `FlowCode` step:

- `LogOS/Theorems/Meta/ObserverFromLogicKernel.agda`

Minimal vocabulary (formal)
---------------------------
The following “physics words” are not metaphors: they are names for concrete, reusable interfaces.

- **System**: a `LogicKernel Sig Q` (shared S/H/code shape plus a parameterised guarded tier).
- **State of knowledge at the boundary**: a boundary constraint `c : Con` in the boundary preorder.
- **Decoded meaning of code**: `decode : Code → Con` from the kernel.
- **Observer step / admissible interaction**: the derived operational step on code
  `FlowCode : Code → Code` (defined as `Guard ∘ Body`).
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
- **Refinement preserves truth** (alignment with the 2-category): if `f ⇒ g` as 2-cells of kernel morphisms,
  then `TruthAt w (mapCode f γ) → TruthAt w (mapCode g γ)` (see
  `ObserverFromLogicKernel.RefinementPreservesTruthAt` and `Meta/RefinementSoundness`).

```agda
  -- Anchor: `TruthAt` expands to `Sat_H_bnd (to∂ w) (decode γ)` by unfolding the definition (proof is `refl`).
open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Kernel.LogicKernel as LK
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObsLK

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
- tensor/whiskering is a monoidal “side-by-side” composition; it can be read as independence/parallelism
  once a model interprets the tensor that way.

Crucially, the process calculus is **ordered**: endomaps are compared by pointwise refinement (`_≤₂_`),
so “being at least as informative / at least as strong” is part of the structure, not a derived notion.
This is the same order that appears as 2-cells in the kernel refinement 2-category:

- `LogOS/Kernel/LogicKernel/Hom2Cat.agda`
- `LogOS/Theorems/CategoryTheory/WrapperCore.agda`
- `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda`
- `LogOS/Theorems/CategoryTheory/Kernel2CatGraded.agda`

This is already the core shape of CQM: a monoidal setting of processes with
parallel and sequential composition, where “systems” are the objects and “processes”
are the morphisms. Symmetry/braiding is optional and lives in explicit algebra packs.

LogOS differs in emphasis: it does not start by postulating a dagger compact category;
it starts by postulating only what the kernel needs (preorders + laxness), and then
lets richer structure be added as explicit packs.

## 3) Non-unitarity and measurement as counted “global events”

A typical physics/quantum split is:

- unitary/local evolution (reversible, information-preserving), vs
- measurement / forgetting / coarse-graining (non-unitary, information-destroying or gaining).

LogOS already has a natural landing pad for exactly this split:

- `LogOS/Domain/Complexity/NonUnitaryCapacity.agda` (count non-unitary events, bound info per event),
- `LogOS/Domain/Complexity/DataProcessingInequality.agda` (DPI interface/axiom pack: channels + an information measure monotone under post-processing),
- `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda` (bundle time + non-unitary + information capacities).

Observer semantics reading:

- “local unitary evolution” lives in the **choice of computation surface** (e.g. circuit stepper),
- “measurement/forgetting” is modeled by a **budgeted global capability** (a separate resource axis),
- “what an observer can conclude” is a theorem of the form:
  *given a budget, no decider/oracle of a certain strength exists*.

This reframes many “no-go” arguments (diagonal/Rice/Tarski style) as **observer-limited**
statements: a fully total oracle would exceed the allowed physical/observational regime.

Quantitative note: in the production kernel, “resource” lives in the adapter `QAdapter` as a
finite‑join unital quantale `Scale`. Sequential composition is modeled by quantale
multiplication (`_·_`), alternative allowances by join (`_⊔s_`), and `⊥s` is the minimal budget.
UniversalIR’s default cost model (`QNat2`) is a two-axis quantale (unitary work vs measurement
events), making “measurement has a counted cost” a first-class notion.

## 4) CQM alignment: what is already present vs what is an extension

What is already structurally present in the production library:

- **Monoidal process shape**: sequential composition + tensor/whiskering at the boundary (`TensorEndo` view).
- **Dagger-shaped hooks**: there is a dedicated meta development around dagger-like structure and positivity
  used by spectral/opacity packs (see `LogOS/Theorems/Meta/Dagger.agda` and related ledgers).
- **Explicit circuit syntax**: UniversalIR includes an explicit circuit language and examples:
  `LogOS/Domain/UniversalIR/Core/QuantumCircuit.agda` and `LogOS/Domain/UniversalIR/Examples/QuantumCircuit.agda`.

What is intentionally *not* built into the kernel (and would be an “extension pack”):

- a full **dagger compact** structure with cups/caps and yanking laws,
- a chosen **CPM/CP\* construction** for mixed-state/observable semantics,
- locality/causality axioms (e.g. a factorization/screening-off law) as default assumptions.

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
   - locality: compositional factorization laws for independent subsystems,
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
- A clearer bridge to CQM and the Deutsch/Aaronson narratives:
  computations are processes; observers are restricted process families; impossibility theorems are resource bounds.

Pointers (where to connect)
---------------------------
- Kernel closure/reflection: `LogOS/Kernel.agda`
- Endomap/tensor DSL: `LogOS/Kernel/TensorDSL.agda`
- Physical budgets: `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda`
- Non-unitary/info axioms: `LogOS/Domain/Complexity/NonUnitaryCapacity.agda`,
  `LogOS/Domain/Complexity/DataProcessingInequality.agda`
- Complexity physical story: `docs/Application_Complexity.lagda.md`
- Circuit surface: `LogOS/Domain/UniversalIR/Core/QuantumCircuit.agda`
