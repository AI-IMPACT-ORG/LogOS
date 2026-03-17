<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Example: ZFC stacks as an explicit refinement inside the Deutsch-style category

This file gives a precise, *in-repo* meaning to the informal slogan:

> “ZFC is a refinement stack on top of a basic Deutsch-style category system.”

The key point is architectural (and fully formalised here):

- the **Deutsch-style category** `LOGᴰ` is obtained from a *shared distributed-semantics ledger*
  `DependentLocalSemantics` by stacking *law ports* (causality + local reversibility)
  as a Σ-totalisation (`DisplayedThin2Cat`); and
- the **ZF/ZFC constructor interface** is presented as a *stack of transformers*
  (a family of `View`s into a shared boundary), and is itself packaged as a
  kernel by the explicit transformation `stackKernel`.

In this example we choose a deliberately minimal shared distributed-semantics ledger:

- a **single region** (`I = ⊤`),
- local observables given by the **set boundary preorder** `SetBnd`, and
- the **identity closure** as the causal doctrine.

This makes the causality and reversibility ports *degenerate*: their laws are
witnessed by definitional equalities/reflexivity (identity closure and pointwise
identity boundary maps), so we do *not* claim any physics. The goal is to
show that the ZF/ZFC stack picture can
be presented as a canonical diagram in a Deutsch-style category by an explicit chain
of transformations. This is therefore a deliberately degenerate architectural
embedding, not evidence that the ZF/ZFC stack carries nontrivial
Deutsch-style locality or reversibility.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Examples.Example_AbstractDeutsch_Category_ZFC where

open import LogOS.API.LT
open import LogOS.API.Ports.PhysicalOptional.Deutsch using (module DeutschSlice)

import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.ZFC as ZFC

-- --------------------------------------------------------------------------
-- ZF: primitive constructors as a Deutsch diagram (single-region semantics).

module ZFInDeutsch {ℓ : Level} (S : ZF.ZFStack {ℓ}) where
  open ZF.ZFStack S

  -- Single-region shared distributed-semantics ledger whose local observable preorder is the
  -- set boundary of the given ZF stack.
  PS : DependentLocalSemantics {lzero} {ℓ} {ℓ}
  PS =
    record
      { I = ⊤
      ; O = λ _ → SetBnd
      ; GC₀ = λ _ → idClosure SetBnd
      }

  Bnd : ConPreorder ℓ ℓ
  Bnd = DependentLocalSemantics.Bnd PS

  constBnd : Con SetBnd → Con Bnd
  constBnd x _ = x

  module Deutsch = DeutschSlice {ℓI = lzero} {ℓOCon = ℓ} {ℓORel = ℓ} {ℓCode = ℓ} PS
  module Loc = Deutsch.Locality
  module Cau = Deutsch.Causality
  module Rev = Deutsch.Reversibility
  module D   = Deutsch.Deutsch

  -- Physical kernels corresponding to the ZF boundary kernel and primitive stack kernel.
  SetKᵖ : Loc.PhysicalKernel
  SetKᵖ =
    record
      { Code = SetU
      ; decode = λ x → constBnd x
      }

  PrimKᵖ : Loc.PhysicalKernel
  PrimKᵖ =
    record
      { Code = Kernel.Code PrimK
      ; decode = λ γ → constBnd (Kernel.decode PrimK γ)
      }

  -- Physical kernel for each primitive operation kernel.
  OpKᵖ : PrimOp → Loc.PhysicalKernel
  OpKᵖ o =
    let K = opKernel primStack o in
    record
      { Code = Kernel.Code K
      ; decode = λ γ → constBnd (Kernel.decode K γ)
      }

  -- The stack injections lift to physical morphisms (boundary map = identity).
  injᵖ
    : (o : PrimOp)
    → Loc.PhysicalHom (OpKᵖ o) PrimKᵖ
  injᵖ o =
    Loc.mkPhysicalHom
      (λ _ x → x)
      (λ _ → idMonoMap {CP = SetBnd})
      (mapCode (injOp primStack o))
      (λ _ → (refl⊑ Bnd , refl⊑ Bnd))

  -- Causality holds by reflexivity under `idClosure`.
  injᵖ-causal
    : (o : PrimOp)
    → KernelHomFlow
        (DependentLocalSemantics.GC PS)
        (DependentLocalSemantics.GC PS)
        (Loc.physicalToKernelHom (injᵖ o))
  injᵖ-causal _ =
    record
      { preserves-Flow = λ _ → refl⊑ Bnd
      }

  -- First package the physical kernels into the causal slice.
  SetKᶜ : Thin2Cat.Obj Cau.WithPort
  SetKᶜ =
    mkTotalObjR
      (Loc.physicalObj SetKᵖ)
      Cau.ttCausal

  PrimKᶜ : Thin2Cat.Obj Cau.WithPort
  PrimKᶜ =
    mkTotalObjR
      (Loc.physicalObj PrimKᵖ)
      Cau.ttCausal

  OpKᶜ : PrimOp → Thin2Cat.Obj Cau.WithPort
  OpKᶜ o =
    mkTotalObjR
      (Loc.physicalObj (OpKᵖ o))
      Cau.ttCausal

  injᶜ
    : (o : PrimOp)
    → Con (Thin2Cat.Hom Cau.WithPort (OpKᶜ o) PrimKᶜ)
  injᶜ o =
    mkTotalHomR
      (injᵖ o)
      (injᵖ-causal o)

  -- Local reversibility then holds because the boundary map is pointwise identity.
  injᶜ-rev
    : (o : PrimOp)
    → Rev.LocalReversible (injᶜ o)
  injᶜ-rev _ =
    record
      { isoAt = λ _ → idOrderIso
      ; forward≈ = λ _ x → (refl⊑ SetBnd , refl⊑ SetBnd)
      }

  -- Finally package the causal diagram into the Deutsch-style category `LOGᴰ PS`.

  SetKᴰ : Thin2Cat.Obj D.WithPort
  SetKᴰ =
    mkTotalObjR
      SetKᶜ
      Rev.ttReversible

  PrimKᴰ : Thin2Cat.Obj D.WithPort
  PrimKᴰ =
    mkTotalObjR
      PrimKᶜ
      Rev.ttReversible

  OpKᴰ : PrimOp → Thin2Cat.Obj D.WithPort
  OpKᴰ o =
    mkTotalObjR
      (OpKᶜ o)
      Rev.ttReversible

  injᴰ
    : (o : PrimOp)
    → Con (Thin2Cat.Hom D.WithPort (OpKᴰ o) PrimKᴰ)
  injᴰ o =
    mkTotalHomR
      (injᶜ o)
      (injᶜ-rev o)

-- --------------------------------------------------------------------------
-- ZFC: refine the primitive constructor stack by adding a choice transformer.

module ZFCInDeutsch {ℓ : Level} (S : ZFC.ZFCStack {ℓ}) where
  open ZFC.ZFCStack S

  -- The same single-region shared distributed-semantics construction works for ZFC,
  -- because the choice transformer is a `View` into the same set boundary.
  PS : DependentLocalSemantics {lzero} {ℓ} {ℓ}
  PS =
    record
      { I = ⊤
      ; O = λ _ → SetBnd
      ; GC₀ = λ _ → idClosure SetBnd
      }

  Bnd : ConPreorder ℓ ℓ
  Bnd = DependentLocalSemantics.Bnd PS

  constBnd : Con SetBnd → Con Bnd
  constBnd x _ = x

  module Deutsch = DeutschSlice {ℓI = lzero} {ℓOCon = ℓ} {ℓORel = ℓ} {ℓCode = ℓ} PS
  module Loc = Deutsch.Locality
  module Cau = Deutsch.Causality
  module Rev = Deutsch.Reversibility
  module D   = Deutsch.Deutsch

  ZFCPrimKᵖ : Loc.PhysicalKernel
  ZFCPrimKᵖ =
    record
      { Code = Kernel.Code PrimKZFC
      ; decode = λ γ → constBnd (Kernel.decode PrimKZFC γ)
      }

  OpKᵖ : Op primStackZFC → Loc.PhysicalKernel
  OpKᵖ o =
    let K = opKernel primStackZFC o in
    record
      { Code = Kernel.Code K
      ; decode = λ γ → constBnd (Kernel.decode K γ)
      }

  injᵖ
    : (o : Op primStackZFC)
    → Loc.PhysicalHom (OpKᵖ o) ZFCPrimKᵖ
  injᵖ o =
    Loc.mkPhysicalHom
      (λ _ x → x)
      (λ _ → idMonoMap {CP = SetBnd})
      (mapCode (injOp primStackZFC o))
      (λ _ → (refl⊑ Bnd , refl⊑ Bnd))

  injᵖ-causal
    : (o : Op primStackZFC)
    → KernelHomFlow
        (DependentLocalSemantics.GC PS)
        (DependentLocalSemantics.GC PS)
        (Loc.physicalToKernelHom (injᵖ o))
  injᵖ-causal _ =
    record
      { preserves-Flow = λ _ → refl⊑ Bnd
      }

  ZFCPrimKᶜ : Thin2Cat.Obj Cau.WithPort
  ZFCPrimKᶜ =
    mkTotalObjR
      (Loc.physicalObj ZFCPrimKᵖ)
      Cau.ttCausal

  OpKᶜ : Op primStackZFC → Thin2Cat.Obj Cau.WithPort
  OpKᶜ o =
    mkTotalObjR
      (Loc.physicalObj (OpKᵖ o))
      Cau.ttCausal

  injᶜ
    : (o : Op primStackZFC)
    → Con (Thin2Cat.Hom Cau.WithPort (OpKᶜ o) ZFCPrimKᶜ)
  injᶜ o =
    mkTotalHomR
      (injᵖ o)
      (injᵖ-causal o)

  injᶜ-rev
    : (o : Op primStackZFC)
    → Rev.LocalReversible (injᶜ o)
  injᶜ-rev _ =
    record
      { isoAt = λ _ → idOrderIso
      ; forward≈ = λ _ x → (refl⊑ SetBnd , refl⊑ SetBnd)
      }

  ZFCPrimKᴰ : Thin2Cat.Obj D.WithPort
  ZFCPrimKᴰ =
    mkTotalObjR
      ZFCPrimKᶜ
      Rev.ttReversible

  OpKᴰ : Op primStackZFC → Thin2Cat.Obj D.WithPort
  OpKᴰ o =
    mkTotalObjR
      (OpKᶜ o)
      Rev.ttReversible

  injᴰ
    : (o : Op primStackZFC)
    → Con (Thin2Cat.Hom D.WithPort (OpKᴰ o) ZFCPrimKᴰ)
  injᴰ o =
    mkTotalHomR
      (injᶜ o)
      (injᶜ-rev o)
```

As intended, every causality/reversibility witness in this file is reflexive
under the single-region identity-closure semantics. The example is about stack
presentation discipline, not about nontrivial physical dynamics.
