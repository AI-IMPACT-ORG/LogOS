<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Communication (LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.Communication where

open import LogOS.API.Architecture as Architecture
open Architecture.Downstream
open Architecture.Kernels using (Kernel)
open import LogOS.Theorems.Boundary.Communication as Comm
```

This page presents the core unification claim in its most operational form:

> unification happens by making *communication* explicit as a typed interface.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

LogOS does this with two bridges that compose:

```text
Code (internal proofs/programs)
  --decode-->  Con_bnd (communicable boundary constraints)
  --Interp-->  Form (an external reporting language)
```

1. **Kernel-as-process (formal commutation).**
   The kernel internalises an admissible one-step evolution on `Code` as
   `FlowCode = Guard ∘ Body`. The kernel also exposes `decode : Code → Con_bnd`.
   The commuting law is part of the kernel interface:
   `decode (Guard γ) ≡ Flow (decode γ)` and `decode (Body γ) ≡ Body∂ (decode γ)`.
   Together these yield `decode (FlowCode γ) ≡ Flow (Body∂ (decode γ))`.

   Interpretation (analogy): you can read `decode` as a “channel” from internal
   code to *communicable boundary constraints*. This does not add semantics: the
   only literal claim is the commutation law above.

2. **Boundary semantics (formal representation).**
   A `BoundarySemantics` instance chooses an external reporting language `Form`
   and an interpretation `Interp : Con_bnd → Form` together with a satisfaction
   equivalence (↔) `Sat∂≈F`. This is a **representation claim**: boundary
   satisfaction and external satisfaction agree up to the provided satisfaction equivalence (↔).

   Interpretation (analogy): you can read `Form` as “what a community can read”,
   but the only literal content is the `Sat∂≈F` interface and theorems phrased
   against it.

If you also want **interop between external boundary logics**, add an import leg:

- `LogOS/Boundary/Port.agda` (`BoundaryPort`: `BoundarySemantics` + `Import` with satisfaction equivalence (↔))
- `LogOS/Ports/Semantic/Interlingua.agda` (canonical translation that preserves and reflects satisfaction (↔) between two ports over the same boundary satisfaction relation)

## The two headline lemmas (paper-friendly)

The file `LogOS/Theorems/Boundary/Communication.agda` packages these ideas as
two named results:

- `Comm.operationalise-strict`:
  strict truth about a formula transports to an external report `Form` via
  the kernel’s S→H translation and the chosen boundary semantics/presentation.

- `Comm.code-channel-commutes`:
  external satisfaction of code after one step agrees with external satisfaction
  of the induced boundary update (decode commutes with evolution, then interpret).

These lemmas are generic: they are stated for an arbitrary kernel `K` and an
arbitrary external boundary semantics/presentation `S` (i.e. a choice of `Form`, `Interp`,
and `Sat∂≈F`). This is where “semantic polymorphism” becomes operational:
you can swap `S` without changing the kernel.

## How to use this in practice

To apply these lemmas, provide:

- a kernel `K : Kernel Sig Q`, and
- a boundary semantics instance `S : BoundarySemantics … (boundaryIO K)`.

Then you can use:

```agda
open import LogOS.Boundary.FromKernel using (boundaryIO)
open import LogOS.Boundary.Semantics using (BoundarySemantics)

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         {ℓForm : Level}
         (K : Kernel Sig Q)
         (S : BoundarySemantics {ℓForm = ℓForm}
               Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
         (w : LogOSSignature.Cosp Sig)
         (φ : Kernel.Fml K)
         (γ : Kernel.Code K)
         where

  ex-operationalise : _
  ex-operationalise = Comm.operationalise-strict K S w φ

  ex-channel-commutes : _
  ex-channel-commutes = Comm.code-channel-commutes K S γ
```

The central message: the library is designed so that “what can be communicated”
is explicit (`BoundaryIO`), swappable (`BoundarySemantics`), and stable under
computation (`FlowCode` commutes with `decode` at one step). Limit/stabilisation
claims (e.g. `μ Flow`, `Th*`) are separate and require explicit ω‑sup/continuity
assumptions.

Related reading:

- For a control/cybernetic reading of the same “compute-then-stabilise” kernel
  interface (budgeted stabilisation as an explicit feedback discipline), see
  `docs/Views/ControlledFeedback.lagda.md`.
- For the meta-theoretic closure/projector view of “what survives communication”
  (maximal Flow-stable truth `Comm⋆`, projector/interior operator `Pr`), see
  `LogOS/Theorems/Meta/CommunicableTruth.agda` and
  `LogOS/Theorems/Meta/BudgetedCommunicableTruth.agda`.
- For how this plugs into self-reference (diagonal) and staging (Futamura) via
  presentation transport, see `docs/DeepDive/FutamuraDiagonal_Showcase.lagda.md`.

Interpretation (analogy): an OO reading (without mutable state)
--------------------------------------------------------------
This is explanatory only (not a formal claim): you can read the architecture in
“OO words” as long as you keep the formal boundaries explicit.

- “Object” = a `Kernel` instance.
- “Interface/port” = boundary I/O + presentations (`BoundaryIO`, `BoundarySemantics`, `BoundaryPort`).
- “Adapter” = canonical translation / view transport (interlingua, reindexing).
- “Composition/wiring” = process/kernels morphisms (scheme categories, kernel homs).
