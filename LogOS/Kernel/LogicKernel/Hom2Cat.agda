{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Hom2Cat where

-- 2-categorical “refinement” view on the CHL-facing `LogicKernel` interface.
--
-- This is the uniform, interface-level version of:
-- - `LogOS.Kernel.Hom2Cat`
-- - `LogOS.Kernel.Graded.Hom2Cat`
--
-- The core 2-cell calculus (whiskering, horizontal composition, ≈-quotient) is
-- obtained by instantiating `LogOS.Kernel.Hom2Cat.Core`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)
import LogOS.Kernel.Hom2Cat.Core as Core
open import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.Hom as KH

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    Obj = LogicKernel Sig Q

    kit : Core.Kit Obj
    kit =
      record
        { conAlgOf        = KH.conAlgOf
        ; Code           = LogicKernel.Code
        ; decode         = LogicKernel.decode
        ; Hom            = KH.LogicKernelHom
        ; con-hom        = KH.LogicKernelHom.con-hom
        ; mapCode        = KH.LogicKernelHom.mapCode
        ; map-decode     = KH.LogicKernelHom.map-decode
        ; idHom          = KH.idLogicKernelHom
        ; composeHom     = KH.composeLogicKernelHom
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
      ( Hom₁        to LogicKernelHom₁
      ; idHom₁      to idLogicKernelHom₁
      ; composeHom₁ to composeLogicKernelHom₁
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

  -- Locally preordered 2-category view (LogicKernel level) and its laws.

  LogicKernelHomPreorder
    : LogicKernel Sig Q → LogicKernel Sig Q → ConPreorder (lsuc (lsuc ℓ))
  LogicKernelHomPreorder K₁ K₂ =
    record
      { Con = LogicKernelHom₁ K₁ K₂
      ; _⊑_ = λ f g → Lift (lsuc (lsuc ℓ)) (f ⇒ g)
      ; refl = λ {f} → lift (refl⇒ f)
      ; trans = λ {f} {g} {h} fg gh →
          lift (trans⇒ {f = f} {g = g} {h = h} (Lift.lower fg) (Lift.lower gh))
      }

  LogicKernelThin2Cat : Thin2Cat (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  LogicKernelThin2Cat =
    record
      { Obj = LogicKernel Sig Q
      ; Hom = LogicKernelHomPreorder
      ; id  = λ {A} → idLogicKernelHom₁ A
      ; _∘_ = _∘₁_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          lift (whisker-left {K₁ = A} {K₂ = B} {K₃ = C} {g = f} {g' = f'} g (Lift.lower le))
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          lift (whisker-right {K₁ = A} {K₂ = B} {K₃ = C} f {f = g} {f' = g'} (Lift.lower le))
      }

  LogicKernelThin2CatLaws : Thin2CatLaws LogicKernelThin2Cat
  LogicKernelThin2CatLaws =
    record
      { id-left = λ f →
          (lift (id-left⇒ f) , lift (id-left⇐ f))
      ; id-right = λ f →
          (lift (id-right⇒ f) , lift (id-right⇐ f))
      ; assoc = λ f g h →
          (lift (assoc⇒ h g f) , lift (assoc⇐ h g f))
      }

  -- Step-grade flow preservation (logic-kernel level).
  --
  -- This is the direct analogue of:
  -- - `KernelHomFlow₁` for ungraded kernels
  -- - `GradedKernelHomFlow₁` for graded kernels
  --
  -- but phrased purely in terms of `LogicKernel.G : GTier` (no GRH-specific infra).

  record LogicKernelHomFlow₁ {K₁ K₂ : LogicKernel Sig Q}
                             (h : LogicKernelHom₁ K₁ K₂)
                             : Set (lsuc ℓ) where
    private
      CP₂   = BulkBoundary.bnd (LogicKernel.BB K₂)
      step₁ = GTier.step (LogicKernel.G K₁)
      step₂ = GTier.step (LogicKernel.G K₂)
      Flow₁ = GTier.Flow (LogicKernel.G K₁)
      Flow₂ = GTier.Flow (LogicKernel.G K₂)
    field
      preserves-step : ∀ c → ConPreorder._⊑_ CP₂ (LogicKernelHom₁.map∂₁ h (Flow₁ step₁ c))
                                         (Flow₂ step₂ (LogicKernelHom₁.map∂₁ h c))

  open LogicKernelHomFlow₁ public

  -- Flow-preserving 1-cells form a sub-2-category (same 2-cells, restricted 1-cells).

  idLogicKernelHomFlow₁
    : ∀ (K : LogicKernel Sig Q)
    → LogicKernelHomFlow₁ (idLogicKernelHom₁ K)
  idLogicKernelHomFlow₁ K =
    record
      { preserves-step = λ _ → ConPreorder.refl (BulkBoundary.bnd (LogicKernel.BB K)) }

  composeLogicKernelHomFlow₁
    : ∀ {K₁ K₂ K₃ : LogicKernel Sig Q}
      {f : LogicKernelHom₁ K₁ K₂}
      {g : LogicKernelHom₁ K₂ K₃}
    → LogicKernelHomFlow₁ f
    → LogicKernelHomFlow₁ g
    → LogicKernelHomFlow₁ (composeLogicKernelHom₁ f g)
  composeLogicKernelHomFlow₁ {K₃ = K₃} {f = f} {g = g} ff gg =
    let
      CP₃  = BulkBoundary.bnd (LogicKernel.BB K₃)
      mapf = LogicKernelHom₁.map∂₁ f
      mapg = LogicKernelHom₁.map∂₁ g
    in
    record
      { preserves-step = λ c →
          let
            step₁ = LogicKernelHomFlow₁.preserves-step ff c
            step₁' = LogicKernelHom₁.mono∂ g step₁
            step₂ = LogicKernelHomFlow₁.preserves-step gg (mapf c)
          in ConPreorder.trans CP₃ step₁' step₂
      }

  module FlowSub₁ =
    FlowSub.With
      (LogicKernel Sig Q)
      LogicKernelHom₁
      LogicKernelHomFlow₁
      idLogicKernelHom₁
      composeLogicKernelHom₁
      idLogicKernelHomFlow₁
      composeLogicKernelHomFlow₁

  open FlowSub₁ public
    renaming
      ( Hom₁ᶠ        to LogicKernelHom₁ᶠ
      ; idHom₁ᶠ      to idLogicKernelHom₁ᶠ
      ; composeHom₁ᶠ to composeLogicKernelHom₁ᶠ
      )

  infix 4 _⇒ᶠ_
  _⇒ᶠ_
    : ∀ {K₁ K₂ : LogicKernel Sig Q}
    → LogicKernelHom₁ᶠ K₁ K₂ → LogicKernelHom₁ᶠ K₁ K₂ → Set ℓ
  _⇒ᶠ_ f g = LogicKernelHom₁ᶠ.hom f ⇒ LogicKernelHom₁ᶠ.hom g
