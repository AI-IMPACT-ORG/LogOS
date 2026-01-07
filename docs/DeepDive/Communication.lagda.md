<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Communication (LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.Communication where

open import LogOS.Prelude
open import LogOS.API.Minimal
open import LogOS.Theorems.Boundary.Communication as Comm
```

This page presents the core unification claim in its most operational form:

> unification happens by making *communication* explicit as a typed interface.

LogOS does this with two bridges that compose:

```text
Code (internal proofs/programs)
  --decode-->  Con_bnd (communicable boundary meaning)
  --Interp-->  Form (an external reporting language)
```

1. **Kernel-as-process (“decode is a channel”).**
   The kernel internalises an admissible one-step evolution on `Code` as
   `FlowCode = Guard ∘ Body`. The kernel also exposes `decode : Code → Con_bnd`.
   The commuting law is part of the kernel interface:
   `decode (Guard γ) ≡ Flow (decode γ)` and `decode (Body γ) ≡ Body∂ (decode γ)`.
   Together these yield `decode (FlowCode γ) ≡ Flow (Body∂ (decode γ))`.

2. **Boundary semantics (“Form is what a community can read”).**
   A `BoundarySemantics` instance chooses an external reporting language `Form`
   and an interpretation `Interp : Con_bnd → Form` together with a satisfaction
   equivalence `Sat∂≈F`. This turns internal truth into externally checkable
   statements.

If you also want **interop between external boundary logics**, add an import leg:

- `LogOS/Boundary/Port.agda` (`BoundaryPort`: `BoundarySemantics` + `Import` with satisfaction equivalence)
- `LogOS/Ports/Semantic/Interlingua.agda` (canonical, meaning-preserving translation between two ports over the same boundary semantics)

## The two headline lemmas (paper-friendly)

The file `LogOS/Theorems/Boundary/Communication.agda` packages these ideas as
two named results:

- `Comm.operationalise-strict`:
  strict truth about a formula transports to an external report `Form` via
  the kernel’s S→H translation and the chosen boundary semantics.

- `Comm.code-channel-commutes`:
  external meaning of code after one step agrees with external meaning of the
  induced boundary update (decode commutes with evolution, then interpret).

These lemmas are generic: they are stated for an arbitrary kernel `K` and an
arbitrary external boundary semantics `S` (i.e. a choice of `Form`, `Interp`,
and `Sat∂≈F`). This is where “semantic polymorphicity” becomes operational:
you can swap `S` without changing the kernel.

## How to use this in practice

To apply these lemmas, provide:

- a kernel `K : Kernel Sig Q`, and
- a boundary semantics instance `S : BoundarySemantics … (boundaryIO K)`.

Then you can use:

```agda
open import LogOS.Kernel.Boundary using (boundaryIO)
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
computation (`FlowCode` commutes with `decode`).
