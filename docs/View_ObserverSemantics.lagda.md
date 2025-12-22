<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Observer Semantics (Physical Reading of LogOS)

```agda
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
- tensor/whiskering is independent or parallel composition (side-by-side systems).

This is already the core shape of CQM: a (symmetric) monoidal setting of processes with
parallel and sequential composition, where “systems” are the objects and “processes”
are the morphisms.

LogOS differs in emphasis: it does not start by postulating a dagger compact category;
it starts by postulating only what the kernel needs (preorders + laxness), and then
lets richer structure be added as explicit packs.

## 3) Non-unitarity and measurement as counted “global events”

A typical physics/quantum split is:

- unitary/local evolution (reversible, information-preserving), vs
- measurement / forgetting / coarse-graining (non-unitary, information-destroying or gaining).

LogOS already has a natural landing pad for exactly this split:

- `LogOS/Domain/Universality/NonUnitaryCapacity.agda` (count non-unitary events, bound info per event),
- `LogOS/Domain/Universality/DataProcessingInequality.agda` (admissible post-processing cannot increase information),
- `LogOS/Domain/Complexity/ObservabilityBudget.agda` (bundle time + non-unitary + information capacities).

Observer semantics reading:

- “local unitary evolution” lives in the **choice of computation surface** (e.g. circuit stepper),
- “measurement/forgetting” is modeled by a **budgeted global capability** (a separate resource axis),
- “what an observer can conclude” is a theorem of the form:
  *given a budget, no decider/oracle of a certain strength exists*.

This reframes many “no-go” arguments (diagonal/Rice/Tarski style) as **observer-limited**
statements: a fully total oracle would exceed the allowed physical/observational regime.

## 4) CQM alignment: what is already present vs what is an extension

What is already structurally present in the production library:

- **Monoidal process shape**: sequential composition + tensor/whiskering at the boundary (`TensorEndo` view).
- **Dagger-shaped hooks**: there is a dedicated meta development around dagger-like structure and positivity
  used by GRH packs (see `LogOS/Theorems/Meta/Dagger.agda` and related GRH ledgers).
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
   - connect observer operations to `ObservabilityBudget` (time + non-unitary + information),
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
- Physical budgets: `LogOS/Domain/Complexity/ObservabilityBudget.agda`
- Non-unitary/info axioms: `LogOS/Domain/Universality/NonUnitaryCapacity.agda`,
  `LogOS/Domain/Universality/DataProcessingInequality.agda`
- P vs NP physical story: `docs/Application_PvsNP.lagda.md`
- Circuit surface: `LogOS/Domain/UniversalIR/Core/QuantumCircuit.agda`
