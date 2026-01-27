{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom2Cat where

-- Lightweight wrapper: instantiate the 2-categorical refinement calculus directly for
-- ungraded kernels.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)

open import LogOS.Kernel
import LogOS.Kernel.Hom as KH
import LogOS.Kernel.Hom2Cat.Core as Core
open import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub

private
  module GC = Truth.GuardedCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    Obj = Kernel Sig Q

    kit : Core.Kit Obj
    kit =
      record
        { conAlgOf        = KH.conAlgOf
        ; Code           = Kernel.Code
        ; decode         = Kernel.decode
        ; Hom            = KH.KernelHom
        ; con-hom        = KH.KernelHom.con-hom
        ; mapCode        = KH.KernelHom.mapCode
        ; map-decode     = KH.KernelHom.map-decode
        ; idHom          = KH.idKernelHom
        ; composeHom     = KH.composeKernelHom
        ; map∂-id        = λ {K} c → KH.map∂-id {K = K} c
        ; map∂-compose   = λ {K₁} {K₂} {K₃} h₁ h₂ c →
                             KH.map∂-compose {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} h₁ h₂ c
        ; mapCode-id     = λ {K} γ → KH.mapCode-id {K = K} γ
        ; mapCode-compose = λ {K₁} {K₂} {K₃} h₁ h₂ γ →
                              KH.mapCode-compose {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} h₁ h₂ γ
        }

    module B = Core.Build kit

  open B public
    renaming
      ( Hom₁        to KernelHom₁
      ; idHom₁      to idKernelHom₁
      ; composeHom₁ to composeKernelHom₁
      ; _∘₁_        to _∘₁_
      ; _⇒_         to _⇒_
      ; refl⇒       to refl⇒
      ; trans⇒      to trans⇒
      ; whiskerL    to whiskerL
      ; whiskerR    to whiskerR
      ; _⊙_         to _⊙_
      ; _≈_         to _≈_
      ; refl≈       to refl≈
      ; sym≈        to sym≈
      ; trans≈      to trans≈
      ; cong-∘₁-≈   to cong-∘₁-≈
      )

  KernelHomPreorder
    : Kernel Sig Q → Kernel Sig Q → ConPreorder (lsuc (lsuc ℓ))
  KernelHomPreorder K₁ K₂ =
    record
      { Con = KernelHom₁ K₁ K₂
      ; _⊑_ = λ f g → Lift (lsuc (lsuc ℓ)) (f ⇒ g)
      ; refl = λ {f} → lift (refl⇒ f)
      ; trans = λ {f} {g} {h} fg gh →
          lift (trans⇒ {f = f} {g = g} {h = h} (Lift.lower fg) (Lift.lower gh))
      }

  -- Locally preordered 2-cat view: kernel morphisms as 1-cells, refinement as 2-cells.
  KernelThin2Cat : Thin2Cat (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  KernelThin2Cat =
    record
      { Obj = Kernel Sig Q
      ; Hom = KernelHomPreorder
      ; id  = λ {A} → idKernelHom₁ A
      ; _∘_ = _∘₁_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          lift (whisker-left {K₁ = A} {K₂ = B} {K₃ = C} {g = f} {g' = f'} g (Lift.lower le))
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          lift (whisker-right {K₁ = A} {K₂ = B} {K₃ = C} f {f = g} {f' = g'} (Lift.lower le))
      }

  KernelThin2CatLaws : Thin2CatLaws KernelThin2Cat
  KernelThin2CatLaws =
    record
      { id-left = λ f →
          (lift (id-left⇒ f) , lift (id-left⇐ f))
      ; id-right = λ f →
          (lift (id-right⇒ f) , lift (id-right⇐ f))
      ; assoc = λ f g h →
          (lift (assoc⇒ h g f) , lift (assoc⇐ h g f))
      }

  -- Extract the underlying `KernelHom` from the 1-cell.
  homKernel
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → KernelHom₁ K₁ K₂ → KH.KernelHom K₁ K₂
  homKernel = KernelHom₁.hom

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
    field
      preserves-step : ∀ c →
        ConPreorder._⊑_ CP₂
          (KernelHom₁.map∂₁ h (Flow₁ c))
          (Flow₂ (KernelHom₁.map∂₁ h c))

  open KernelHomFlow₁ public

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
      { preserves-step = FH.preserves-F }

  idKernelHomFlow₁ : ∀ (K : Kernel Sig Q) → KernelHomFlow₁ (idKernelHom₁ K)
  idKernelHomFlow₁ K =
    record
      { preserves-step = λ _ → ConPreorder.refl (BulkBoundary.bnd (Kernel.BB K)) }

  composeKernelHomFlow₁
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      {f : KernelHom₁ K₁ K₂} {g : KernelHom₁ K₂ K₃}
    → KernelHomFlow₁ f → KernelHomFlow₁ g → KernelHomFlow₁ (g ∘₁ f)
  composeKernelHomFlow₁ {K₃ = K₃} {f = f} {g = g} ff gg =
    let
      CP₃  = BulkBoundary.bnd (Kernel.BB K₃)
      mapf = KernelHom₁.map∂₁ f
    in
    record
      { preserves-step = λ c →
          let
            step₁ = KernelHomFlow₁.preserves-step ff c
            step₁' = KernelHom₁.mono∂ g step₁
            step₂ = KernelHomFlow₁.preserves-step gg (mapf c)
          in ConPreorder.trans CP₃ step₁' step₂
      }

  module FlowSub₁ =
    FlowSub.With
      (Kernel Sig Q)
      KernelHom₁
      KernelHomFlow₁
      idKernelHom₁
      composeKernelHom₁
      idKernelHomFlow₁
      composeKernelHomFlow₁

  open FlowSub₁ public
    renaming
      ( Hom₁ᶠ        to KernelHom₁ᶠ
      ; idHom₁ᶠ      to idKernelHom₁ᶠ
      ; composeHom₁ᶠ to composeKernelHom₁ᶠ
      )
