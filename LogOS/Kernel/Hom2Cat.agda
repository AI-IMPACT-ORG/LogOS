{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom2Cat where

-- Thin wrapper: the 2-categorical refinement calculus is defined once for the
-- CHL-facing `LogicKernel` interface, and ungraded kernels embed via
-- `LogicKernel.FromKernel.asLogicKernel`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.FromKernel as LKFrom
import LogOS.Kernel.Hom as KH
import LogOS.Kernel.LogicKernel.Hom as LKH
import LogOS.Kernel.LogicKernel.Hom2Cat as LK2

private
  module GC = Truth.GuardedCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    asLK = LKFrom.asLogicKernel

  -- 2-category (and ≈-quotient) structure: inherited from `LogicKernel.Hom2Cat`
  -- by restricting objects to the image of `asLK`.

  KernelHom₁ : Kernel Sig Q → Kernel Sig Q → Set (lsuc (lsuc ℓ))
  KernelHom₁ K₁ K₂ = LK2.LogicKernelHom₁ (asLK K₁) (asLK K₂)

  idKernelHom₁ : (K : Kernel Sig Q) → KernelHom₁ K K
  idKernelHom₁ K = LK2.idLogicKernelHom₁ (asLK K)

  composeKernelHom₁
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
    → KernelHom₁ K₁ K₂ → KernelHom₁ K₂ K₃ → KernelHom₁ K₁ K₃
  composeKernelHom₁ f g = LK2.composeLogicKernelHom₁ f g

  infixr 9 _∘₁_
  _∘₁_
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
    → KernelHom₁ K₂ K₃ → KernelHom₁ K₁ K₂ → KernelHom₁ K₁ K₃
  _∘₁_ = LK2._∘₁_

  infix 4 _⇒_
  _⇒_
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → KernelHom₁ K₁ K₂ → KernelHom₁ K₁ K₂ → Set ℓ
  _⇒_ = LK2._⇒_

  refl⇒ : ∀ {K₁ K₂ : Kernel Sig Q} (f : KernelHom₁ K₁ K₂) → f ⇒ f
  refl⇒ = LK2.refl⇒

  trans⇒
    : ∀ {K₁ K₂ : Kernel Sig Q} {f g h : KernelHom₁ K₁ K₂}
    → f ⇒ g → g ⇒ h → f ⇒ h
  trans⇒ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} {h = h} fg gh =
    LK2.trans⇒ {K₁ = asLK K₁} {K₂ = asLK K₂} {f = f} {g = g} {h = h} fg gh

  whiskerR
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      {g g' : KernelHom₁ K₂ K₃}
      (f : KernelHom₁ K₁ K₂)
    → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f)
  whiskerR {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg' =
    LK2.whiskerR {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃} {g = g} {g' = g'} f gg'

  whiskerL
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      (g : KernelHom₁ K₂ K₃)
      {f f' : KernelHom₁ K₁ K₂}
    → f ⇒ f' → (g ∘₁ f) ⇒ (g ∘₁ f')
  whiskerL {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff' =
    LK2.whiskerL {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃} g {f = f} {f' = f'} ff'

  infixr 9 _⊙_
  _⊙_
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      {f f' : KernelHom₁ K₁ K₂}
      {g g' : KernelHom₁ K₂ K₃}
    → f ⇒ f' → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f')
  _⊙_ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg' =
    LK2._⊙_ {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg'

  infix 4 _≈_
  _≈_
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → KernelHom₁ K₁ K₂ → KernelHom₁ K₁ K₂ → Set ℓ
  _≈_ = LK2._≈_

  refl≈ : ∀ {K₁ K₂ : Kernel Sig Q} (f : KernelHom₁ K₁ K₂) → f ≈ f
  refl≈ = LK2.refl≈

  sym≈ : ∀ {K₁ K₂ : Kernel Sig Q} {f g : KernelHom₁ K₁ K₂} → f ≈ g → g ≈ f
  sym≈ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} fg =
    LK2.sym≈ {K₁ = asLK K₁} {K₂ = asLK K₂} {f = f} {g = g} fg

  trans≈
    : ∀ {K₁ K₂ : Kernel Sig Q} {f g h : KernelHom₁ K₁ K₂}
    → f ≈ g → g ≈ h → f ≈ h
  trans≈ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} {h = h} fg gh =
    LK2.trans≈ {K₁ = asLK K₁} {K₂ = asLK K₂} {f = f} {g = g} {h = h} fg gh

  cong-∘₁-≈
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      {f f' : KernelHom₁ K₁ K₂}
      {g g' : KernelHom₁ K₂ K₃}
    → f ≈ f' → g ≈ g' → (g ∘₁ f) ≈ (g' ∘₁ f')
  cong-∘₁-≈ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff gg =
    LK2.cong-∘₁-≈ {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff gg

  -- Extract the underlying `KernelHom` from the logic-kernel-level 1-cell.

  homKernel
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → KernelHom₁ K₁ K₂ → KH.KernelHom K₁ K₂
  homKernel h =
    let hlk = LK2.LogicKernelHom₁.hom h in
    record
      { con-hom    = LKH.LogicKernelHom.con-hom hlk
      ; mapCode    = LKH.LogicKernelHom.mapCode hlk
      ; map-encode = LKH.LogicKernelHom.map-encode hlk
      ; map-decode = LKH.LogicKernelHom.map-decode hlk
      }

  -- Step-grade (i.e. unique-step) flow preservation, in a composable form.
  --
  -- For kernels, the G-tier has a single implicit step, so this is exactly the
  -- “preserves Flow” story; we expose both names.

  record KernelHomFlow₁ {K₁ K₂ : Kernel Sig Q}
                        (h : KernelHom₁ K₁ K₂) : Set (lsuc ℓ) where
    private
      CP₂ = BulkBoundary.bnd (Kernel.BB K₂)
      Flow₁ = GC.GuardedClosure.Flow (Kernel.GTruth K₁)
      Flow₂ = GC.GuardedClosure.Flow (Kernel.GTruth K₂)
      Th⋆₁  = GC.GuardedClosure.Th* (Kernel.GTruth K₁)
      Th⋆₂  = GC.GuardedClosure.Th* (Kernel.GTruth K₂)
    field
      preserves-step : ∀ c →
        ConPoset._⊑_ CP₂
          (LK2.LogicKernelHom₁.map∂₁ h (Flow₁ c))
          (Flow₂ (LK2.LogicKernelHom₁.map∂₁ h c))
      preserves-Th : ConPoset._⊑_ CP₂ (LK2.LogicKernelHom₁.map∂₁ h Th⋆₁) Th⋆₂

    preserves-F = preserves-step

  open KernelHomFlow₁ public

  toLKFlow
    : ∀ {K₁ K₂ : Kernel Sig Q} {h : KernelHom₁ K₁ K₂}
    → KernelHomFlow₁ h → LK2.LogicKernelHomFlow₁ h
  toLKFlow hf =
    record
      { preserves-step = KernelHomFlow₁.preserves-step hf
      ; preserves-Th   = KernelHomFlow₁.preserves-Th hf
      }

  fromLKFlow
    : ∀ {K₁ K₂ : Kernel Sig Q} {h : KernelHom₁ K₁ K₂}
    → LK2.LogicKernelHomFlow₁ h → KernelHomFlow₁ h
  fromLKFlow hf =
    record
      { preserves-step = LK2.LogicKernelHomFlow₁.preserves-step hf
      ; preserves-Th   = LK2.LogicKernelHomFlow₁.preserves-Th hf
      }

  fromKernelHomFlow
    : ∀ {K₁ K₂ : Kernel Sig Q}
      (h : KernelHom₁ K₁ K₂)
    → KH.KernelHomFlow K₁ K₂ (homKernel h)
    → KernelHomFlow₁ h
  fromKernelHomFlow h hf =
    let
      open KH.KernelHomFlow hf
      module FH = GC.FlowHom flow-hom
    in
    record
      { preserves-step = FH.preserves-F
      ; preserves-Th   = FH.preserves-Th
      }

  idKernelHomFlow₁ : ∀ (K : Kernel Sig Q) → KernelHomFlow₁ (idKernelHom₁ K)
  idKernelHomFlow₁ K = fromLKFlow (LK2.idLogicKernelHomFlow₁ (asLK K))

  composeKernelHomFlow₁
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      {f : KernelHom₁ K₁ K₂} {g : KernelHom₁ K₂ K₃}
    → KernelHomFlow₁ f → KernelHomFlow₁ g → KernelHomFlow₁ (g ∘₁ f)
  composeKernelHomFlow₁ ff gg =
    fromLKFlow (LK2.composeLogicKernelHomFlow₁ (toLKFlow ff) (toLKFlow gg))

  -- Flow-preserving 1-cells: reuse the `LogicKernel` FlowSub 2-category and
  -- restrict objects to the image of `asLK`.

  KernelHom₁ᶠ : Kernel Sig Q → Kernel Sig Q → Set (lsuc (lsuc ℓ))
  KernelHom₁ᶠ K₁ K₂ = LK2.LogicKernelHom₁ᶠ (asLK K₁) (asLK K₂)

  idKernelHom₁ᶠ : (K : Kernel Sig Q) → KernelHom₁ᶠ K K
  idKernelHom₁ᶠ K = LK2.idLogicKernelHom₁ᶠ (asLK K)

  composeKernelHom₁ᶠ
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
    → KernelHom₁ᶠ K₁ K₂ → KernelHom₁ᶠ K₂ K₃ → KernelHom₁ᶠ K₁ K₃
  composeKernelHom₁ᶠ f g = LK2.composeLogicKernelHom₁ᶠ f g
