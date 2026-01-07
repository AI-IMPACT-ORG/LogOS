{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.EndoCore where

-- Boundary endomaps and pointwise refinements for a given `LogicKernel` K.
-- This is the base layer shared by:
-- - the Flow-specialised DSL in `LogicKernel.Endo`, and
-- - the modality-relative DSL in `LogicKernel.EndoRelative`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.LogicKernel

infix 4 _≤₂_
infixr 9 _∘E_

record Endo {ℓ : Level}
            {Sig : LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            (K   : LogicKernel Sig Q)
            : Set (lsuc ℓ) where
  open LogicKernel K
  private
    Con∂ = ConPoset.Con (BulkBoundary.bnd BB)
    _≤_  = ConPoset._⊑_ (BulkBoundary.bnd BB)
  field
    fn   : Con∂ → Con∂
    mono : ∀ {x y} → x ≤ y → fn x ≤ fn y

open Endo public

-- Pointwise refinement between endomaps.
_≤₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : LogicKernel Sig Q) → Endo K → Endo K → Set ℓ
_≤₂_ {ℓ} {Sig} {Q} K f g = ∀ c →
  let open LogicKernel K in
  ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn f c) (Endo.fn g c)

-- Identity and composition on endomaps.

idEndo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : LogicKernel Sig Q) → Endo K
idEndo K .Endo.fn   = λ c → c
idEndo K .Endo.mono = λ p → p

_∘E_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       {K : LogicKernel Sig Q} → Endo K → Endo K → Endo K
_∘E_ {K = K} f g .Endo.fn   = λ c → Endo.fn f (Endo.fn g c)
_∘E_ {K = K} f g .Endo.mono = λ p → Endo.mono f (Endo.mono g p)

-- Refinement basics.

refl₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
        (K : LogicKernel Sig Q) (f : Endo K) → _≤₂_ K f f
refl₂ K f = λ _ →
  let open LogicKernel K in
  ConPoset.refl (BulkBoundary.bnd BB)

trans₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : LogicKernel Sig Q)
         {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K g h → _≤₂_ K f h
trans₂ K fg gh = λ c →
  let open LogicKernel K in
  ConPoset.trans (BulkBoundary.bnd BB) (fg c) (gh c)

-- Whiskering: composition preserves refinement on either side.

whisker-left : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
               (K : LogicKernel Sig Q)
               {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K (h ∘E f) (h ∘E g)
whisker-left K {f} {g} {h} fg = λ c → Endo.mono h (fg c)

whisker-right : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                (K : LogicKernel Sig Q)
                {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K (f ∘E h) (g ∘E h)
whisker-right K {f} {g} {h} fg = λ c → fg (Endo.fn h c)

