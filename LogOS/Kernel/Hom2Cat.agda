{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom2Cat where

-- 2-categorical “refinement” view on the CHL-facing `Kernel` interface.
--
-- This is the ungraded (kernel-level) instance; for the graded analogue see
-- `LogOS.Kernel.Graded.Hom2Cat`.
--
-- The core 2-cell calculus (whiskering, horizontal composition, ≈-quotient) is
-- obtained by instantiating `LogOS.Kernel.Hom2Cat.Core`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder)
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Minimal.RelThin2Cat using (RelThin2Cat; RelThin2CatLaws)
import LogOS.Kernel.Hom2Cat.Core as Core
open import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub
open import LogOS.Kernel
open import LogOS.Kernel.Hom as KH

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

  -- Locally preordered 2-category view (Kernel level) and its laws.

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

  -- RelPreorder-enriched 2-category view (no `Lift` needed).

  KernelHomRelPreorder
    : Kernel Sig Q → Kernel Sig Q → RelPreorder (lsuc (lsuc ℓ)) ℓ
  KernelHomRelPreorder K₁ K₂ =
    record
      { Con = KernelHom₁ K₁ K₂
      ; _⊑_ = λ f g → f ⇒ g
      ; refl = λ {f} → refl⇒ f
      ; trans = λ {f} {g} {h} fg gh → trans⇒ {f = f} {g = g} {h = h} fg gh
      }

  KernelRelThin2Cat : RelThin2Cat (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)) ℓ
  KernelRelThin2Cat =
    record
      { Obj = Kernel Sig Q
      ; Hom = KernelHomRelPreorder
      ; id  = λ {A} → idKernelHom₁ A
      ; _∘_ = _∘₁_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          whisker-left {K₁ = A} {K₂ = B} {K₃ = C} {g = f} {g' = f'} g le
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          whisker-right {K₁ = A} {K₂ = B} {K₃ = C} f {f = g} {f' = g'} le
      }

  KernelRelThin2CatLaws : RelThin2CatLaws KernelRelThin2Cat
  KernelRelThin2CatLaws =
    record
      { id-left = λ f → (id-left⇒ f , id-left⇐ f)
      ; id-right = λ f → (id-right⇒ f , id-right⇐ f)
      ; assoc = λ f g h → (assoc⇒ h g f , assoc⇐ h g f)
      }

  -- Step-grade flow preservation (logic-kernel level).
  --
  -- This is the direct analogue of:
  -- - `KernelHomFlow₁` for ungraded kernels
  -- - `GradedKernelHomFlow₁` for graded kernels
  --
  -- but phrased purely in terms of `Kernel.G : GTier` (no GRH-specific infra).

  record KernelHomFlow₁ {K₁ K₂ : Kernel Sig Q}
                             (h : KernelHom₁ K₁ K₂)
                             : Set (lsuc ℓ) where
    private
      CP₂   = BulkBoundary.bnd (Kernel.BB K₂)
      step₁ = GTier.step (Kernel.G K₁)
      step₂ = GTier.step (Kernel.G K₂)
      Flow₁ = GTier.Flow (Kernel.G K₁)
      Flow₂ = GTier.Flow (Kernel.G K₂)
    field
      preserves-step : ∀ c → ConPreorder._⊑_ CP₂ (KernelHom₁.map∂₁ h (Flow₁ step₁ c))
                                         (Flow₂ step₂ (KernelHom₁.map∂₁ h c))

  open KernelHomFlow₁ public

  -- Flow-preserving 1-cells form a sub-2-category (same 2-cells, restricted 1-cells).

  idKernelHomFlow₁
    : ∀ (K : Kernel Sig Q)
    → KernelHomFlow₁ (idKernelHom₁ K)
  idKernelHomFlow₁ K =
    record
      { preserves-step = λ _ → ConPreorder.refl (BulkBoundary.bnd (Kernel.BB K)) }

  composeKernelHomFlow₁
    : ∀ {K₁ K₂ K₃ : Kernel Sig Q}
      {f : KernelHom₁ K₁ K₂}
      {g : KernelHom₁ K₂ K₃}
    → KernelHomFlow₁ f
    → KernelHomFlow₁ g
    → KernelHomFlow₁ (composeKernelHom₁ f g)
  composeKernelHomFlow₁ {K₃ = K₃} {f = f} {g = g} ff gg =
    let
      CP₃  = BulkBoundary.bnd (Kernel.BB K₃)
      mapf = KernelHom₁.map∂₁ f
      mapg = KernelHom₁.map∂₁ g
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

  infix 4 _⇒ᶠ_
  _⇒ᶠ_
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → KernelHom₁ᶠ K₁ K₂ → KernelHom₁ᶠ K₁ K₂ → Set ℓ
  _⇒ᶠ_ f g = KernelHom₁ᶠ.hom f ⇒ KernelHom₁ᶠ.hom g
