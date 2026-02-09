{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Hom2Cat where

-- 2-categorical “refinement” view on graded-kernel morphisms.
--
-- Implementation note: the 2-cell calculus is defined once for the CHL-facing
-- `Kernel` interface (`LogOS.Kernel.Hom2Cat`). This module is
-- a lightweight wrapper that:
-- - embeds graded kernels via `FromGradedKernel.asKernel`;
-- - reuses the `Kernel` 2-cell calculus by translating 1-cells.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.ConAlg using (ConAlgHom≡)
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Minimal.RelThin2Cat using (RelThin2Cat; RelThin2CatLaws)

open import LogOS.Kernel.Graded
open import LogOS.Kernel
import LogOS.Kernel.FromGradedKernel as FromGraded
open import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub
import LogOS.Kernel.Graded.Hom as KH
import LogOS.Kernel.Hom as LKH
import LogOS.Kernel.Hom2Cat as LK2

private
  module GC = Truth.GuardedCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    asKernel : GradedKernel Sig Q → Kernel Sig Q
    asKernel = FromGraded.asKernel

    toKernelHom
      : ∀ {K₁ K₂ : GradedKernel Sig Q}
      → KH.GradedKernelHom K₁ K₂ → LKH.KernelHom (asKernel K₁) (asKernel K₂)
    toKernelHom h = record
      { con-hom    = KH.GradedKernelHom.con-hom h
      ; mapCode    = KH.GradedKernelHom.mapCode h
      ; map-encode = KH.GradedKernelHom.map-encode h
      ; map-decode = KH.GradedKernelHom.map-decode h
      }

    fromKernelHom
      : ∀ {K₁ K₂ : GradedKernel Sig Q}
      → LKH.KernelHom (asKernel K₁) (asKernel K₂) → KH.GradedKernelHom K₁ K₂
    fromKernelHom h = record
      { con-hom    = LKH.KernelHom.con-hom h
      ; mapCode    = LKH.KernelHom.mapCode h
      ; map-encode = LKH.KernelHom.map-encode h
      ; map-decode = LKH.KernelHom.map-decode h
      }

  record GradedKernelHom₁ (K₁ K₂ : GradedKernel Sig Q) : Set (lsuc (lsuc ℓ)) where
    private
      CP₁ = BulkBoundary.bnd (GradedKernel.BB K₁)
      CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
    field
      hom   : KH.GradedKernelHom K₁ K₂
      mono∂ :
        ∀ {c c'}
        → ConPreorder._⊑_ CP₁ c c'
        → ConPreorder._⊑_ CP₂ (ConAlgHom≡.map∂ (KH.GradedKernelHom.con-hom hom) c)
                           (ConAlgHom≡.map∂ (KH.GradedKernelHom.con-hom hom) c')

    map∂₁ : ConPreorder.Con CP₁ → ConPreorder.Con CP₂
    map∂₁ = ConAlgHom≡.map∂ (KH.GradedKernelHom.con-hom hom)

    mapCode₁ : GradedKernel.Code K₁ → GradedKernel.Code K₂
    mapCode₁ = KH.GradedKernelHom.mapCode hom

    map-decode₁ : ∀ γ → GradedKernel.decode K₂ (mapCode₁ γ) ≡ map∂₁ (GradedKernel.decode K₁ γ)
    map-decode₁ = KH.GradedKernelHom.map-decode hom

  open GradedKernelHom₁ public

  toKernelHom₁
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → LK2.KernelHom₁ (asKernel K₁) (asKernel K₂)
  toKernelHom₁ h =
    record
      { hom   = toKernelHom (GradedKernelHom₁.hom h)
      ; mono∂ = GradedKernelHom₁.mono∂ h
      }

  fromKernelHom₁
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → LK2.KernelHom₁ (asKernel K₁) (asKernel K₂) → GradedKernelHom₁ K₁ K₂
  fromKernelHom₁ h =
    record
      { hom   = fromKernelHom (LK2.KernelHom₁.hom h)
      ; mono∂ = LK2.KernelHom₁.mono∂ h
      }

  idGradedKernelHom₁ : ∀ (K : GradedKernel Sig Q) → GradedKernelHom₁ K K
  idGradedKernelHom₁ K = fromKernelHom₁ (LK2.idKernelHom₁ (asKernel K))

  composeGradedKernelHom₁
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₂ K₃ → GradedKernelHom₁ K₁ K₃
  composeGradedKernelHom₁ f g =
    fromKernelHom₁ (LK2.composeKernelHom₁ (toKernelHom₁ f) (toKernelHom₁ g))

  infixr 9 _∘₁_
  _∘₁_
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₂ K₃ → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₃
  g ∘₁ f = composeGradedKernelHom₁ f g

  -- 2-cells: reuse the `Kernel` calculus after translating 1-cells.

  infix 4 _⇒_
  _⇒_
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₂ → Set ℓ
  f ⇒ g = LK2._⇒_ (toKernelHom₁ f) (toKernelHom₁ g)

  -- Named alias: decode-quotiented refinement (2-cells).
  --
  -- This is the default notion used by the 2-cell calculus: it compares 1-cells
  -- only on the decoded image of code.
  RefinesDecode
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₂ → Set ℓ
  RefinesDecode = _⇒_

  -- Stronger (non-quotiented) refinement: pointwise on all boundary constraints.
  Refines∂
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₂ → Set ℓ
  Refines∂ f g = LK2.Refines∂ (toKernelHom₁ f) (toKernelHom₁ g)

  Refines∂→RefinesDecode
    : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g : GradedKernelHom₁ K₁ K₂}
    → Refines∂ f g
    → RefinesDecode f g
  Refines∂→RefinesDecode {f = f} {g = g} le =
    LK2.Refines∂→RefinesDecode {f = toKernelHom₁ f} {g = toKernelHom₁ g} le

  refl⇒ : ∀ {K₁ K₂ : GradedKernel Sig Q} (f : GradedKernelHom₁ K₁ K₂) → f ⇒ f
  refl⇒ f = LK2.refl⇒ (toKernelHom₁ f)

  trans⇒
    : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g h : GradedKernelHom₁ K₁ K₂}
    → f ⇒ g → g ⇒ h → f ⇒ h
  trans⇒ {f = f} {g = g} {h = h} fg gh =
    LK2.trans⇒ {f = toKernelHom₁ f} {g = toKernelHom₁ g} {h = toKernelHom₁ h} fg gh

  whiskerR
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {g g' : GradedKernelHom₁ K₂ K₃}
      (f : GradedKernelHom₁ K₁ K₂)
    → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f)
  whiskerR {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg' =
    LK2.whiskerR
      {K₁ = asKernel K₁} {K₂ = asKernel K₂} {K₃ = asKernel K₃}
      {g = toKernelHom₁ g} {g' = toKernelHom₁ g'}
      (toKernelHom₁ f)
      gg'

  whiskerL
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      (g : GradedKernelHom₁ K₂ K₃)
      {f f' : GradedKernelHom₁ K₁ K₂}
    → f ⇒ f' → (g ∘₁ f) ⇒ (g ∘₁ f')
  whiskerL {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff' =
    LK2.whiskerL
      {K₁ = asKernel K₁} {K₂ = asKernel K₂} {K₃ = asKernel K₃}
      (toKernelHom₁ g)
      {f = toKernelHom₁ f} {f' = toKernelHom₁ f'}
      ff'

  -- Naming alignment with Thin2Cat: left/right refers to the varying 1-cell.
  whisker-left
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {g g' : GradedKernelHom₁ K₂ K₃}
      (f : GradedKernelHom₁ K₁ K₂)
    → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f)
  whisker-left {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg' =
    whiskerR {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg'

  whisker-right
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      (g : GradedKernelHom₁ K₂ K₃)
      {f f' : GradedKernelHom₁ K₁ K₂}
    → f ⇒ f' → (g ∘₁ f) ⇒ (g ∘₁ f')
  whisker-right {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff' =
    whiskerL {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff'

  GradedKernelHomPreorder
    : GradedKernel Sig Q → GradedKernel Sig Q → ConPreorder (lsuc (lsuc ℓ))
  GradedKernelHomPreorder K₁ K₂ =
    record
      { Con = GradedKernelHom₁ K₁ K₂
      ; _⊑_ = λ f g → Lift (lsuc (lsuc ℓ)) (f ⇒ g)
      ; refl = λ {f} → lift (refl⇒ f)
      ; trans = λ {f} {g} {h} fg gh →
          lift (trans⇒ {f = f} {g = g} {h = h} (Lift.lower fg) (Lift.lower gh))
      }

  GradedKernelThin2Cat : Thin2Cat (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  GradedKernelThin2Cat =
    record
      { Obj = GradedKernel Sig Q
      ; Hom = GradedKernelHomPreorder
      ; id  = λ {A} → idGradedKernelHom₁ A
      ; _∘_ = _∘₁_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          lift (whisker-left {K₁ = A} {K₂ = B} {K₃ = C} {g = f} {g' = f'} g (Lift.lower le))
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          lift (whisker-right {K₁ = A} {K₂ = B} {K₃ = C} f {f = g} {f' = g'} (Lift.lower le))
      }

  GradedKernelThin2CatLaws : Thin2CatLaws GradedKernelThin2Cat
  GradedKernelThin2CatLaws =
    record
      { id-left = λ {A} {B} f →
          ( lift (LK2.id-left⇒ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f))
          , lift (LK2.id-left⇐ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f))
          )
      ; id-right = λ {A} {B} f →
          ( lift (LK2.id-right⇒ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f))
          , lift (LK2.id-right⇐ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f))
          )
      ; assoc = λ {A} {B} {C} {D} f g h →
          ( lift (LK2.assoc⇒ {K₁ = asKernel A} {K₂ = asKernel B} {K₃ = asKernel C} {K₄ = asKernel D}
                    (toKernelHom₁ h) (toKernelHom₁ g) (toKernelHom₁ f))
          , lift (LK2.assoc⇐ {K₁ = asKernel A} {K₂ = asKernel B} {K₃ = asKernel C} {K₄ = asKernel D}
                    (toKernelHom₁ h) (toKernelHom₁ g) (toKernelHom₁ f))
          )
      }

  -- RelPreorder-enriched 2-category view (no `Lift` needed).

  GradedKernelHomRelPreorder
    : GradedKernel Sig Q → GradedKernel Sig Q → RelPreorder (lsuc (lsuc ℓ)) ℓ
  GradedKernelHomRelPreorder K₁ K₂ =
    record
      { Con = GradedKernelHom₁ K₁ K₂
      ; _⊑_ = λ f g → f ⇒ g
      ; refl = λ {f} → refl⇒ f
      ; trans = λ {f} {g} {h} fg gh → trans⇒ {f = f} {g = g} {h = h} fg gh
      }

  GradedKernelRelThin2Cat : RelThin2Cat (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)) ℓ
  GradedKernelRelThin2Cat =
    record
      { Obj = GradedKernel Sig Q
      ; Hom = GradedKernelHomRelPreorder
      ; id  = λ {A} → idGradedKernelHom₁ A
      ; _∘_ = _∘₁_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          whisker-left {K₁ = A} {K₂ = B} {K₃ = C} {g = f} {g' = f'} g le
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          whisker-right {K₁ = A} {K₂ = B} {K₃ = C} f {f = g} {f' = g'} le
      }

  GradedKernelRelThin2CatLaws : RelThin2CatLaws GradedKernelRelThin2Cat
  GradedKernelRelThin2CatLaws =
    record
      { id-left = λ {A} {B} f →
          ( LK2.id-left⇒ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f)
          , LK2.id-left⇐ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f)
          )
      ; id-right = λ {A} {B} f →
          ( LK2.id-right⇒ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f)
          , LK2.id-right⇐ {K₁ = asKernel A} {K₂ = asKernel B} (toKernelHom₁ f)
          )
      ; assoc = λ {A} {B} {C} {D} f g h →
          ( LK2.assoc⇒ {K₁ = asKernel A} {K₂ = asKernel B} {K₃ = asKernel C} {K₄ = asKernel D}
              (toKernelHom₁ h) (toKernelHom₁ g) (toKernelHom₁ f)
          , LK2.assoc⇐ {K₁ = asKernel A} {K₂ = asKernel B} {K₃ = asKernel C} {K₄ = asKernel D}
              (toKernelHom₁ h) (toKernelHom₁ g) (toKernelHom₁ f)
          )
      }

  infixl 7 _⊙_
  _⊙_
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {f f' : GradedKernelHom₁ K₁ K₂}
      {g g' : GradedKernelHom₁ K₂ K₃}
    → f ⇒ f' → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f')
  _⊙_ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg' =
    LK2._⊙_
      {K₁ = asKernel K₁} {K₂ = asKernel K₂} {K₃ = asKernel K₃}
      {f = toKernelHom₁ f} {f' = toKernelHom₁ f'} {g = toKernelHom₁ g} {g' = toKernelHom₁ g'}
      ff'
      gg'

  -- Mutual refinement (2-cell equivalence).

  infix 4 _≈_
  _≈_
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₂ → Set ℓ
  f ≈ g = LK2._≈_ (toKernelHom₁ f) (toKernelHom₁ g)

  refl≈ : ∀ {K₁ K₂ : GradedKernel Sig Q} (f : GradedKernelHom₁ K₁ K₂) → f ≈ f
  refl≈ f = LK2.refl≈ (toKernelHom₁ f)

  sym≈ : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g : GradedKernelHom₁ K₁ K₂} → f ≈ g → g ≈ f
  sym≈ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} fg =
    LK2.sym≈ {K₁ = asKernel K₁} {K₂ = asKernel K₂} {f = toKernelHom₁ f} {g = toKernelHom₁ g} fg

  trans≈
    : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g h : GradedKernelHom₁ K₁ K₂}
    → f ≈ g → g ≈ h → f ≈ h
  trans≈ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} {h = h} fg gh =
    LK2.trans≈ {K₁ = asKernel K₁} {K₂ = asKernel K₂} {f = toKernelHom₁ f} {g = toKernelHom₁ g} {h = toKernelHom₁ h} fg gh

  cong-∘₁-≈
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {f f' : GradedKernelHom₁ K₁ K₂}
      {g g' : GradedKernelHom₁ K₂ K₃}
    → f ≈ f'
    → g ≈ g'
    → (g ∘₁ f) ≈ (g' ∘₁ f')
  cong-∘₁-≈ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff gg =
    LK2.cong-∘₁-≈
      {K₁ = asKernel K₁} {K₂ = asKernel K₂} {K₃ = asKernel K₃}
      {f = toKernelHom₁ f} {f' = toKernelHom₁ f'} {g = toKernelHom₁ g} {g' = toKernelHom₁ g'}
      ff gg

  -- Step-grade flow preservation, in a composable form (once a 1-cell supplies `mono∂`).

  record GradedKernelHomFlow₁ {K₁ K₂ : GradedKernel Sig Q}
                              (h : GradedKernelHom₁ K₁ K₂)
                              : Set (lsuc ℓ) where
    private
      CP₂   = BulkBoundary.bnd (GradedKernel.BB K₂)
      step₁ = GradedKernel.step-grade K₁
      step₂ = GradedKernel.step-grade K₂
      Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)
      Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
    field
      preserves-step : ∀ c →
        ConPreorder._⊑_ CP₂ (GradedKernelHom₁.map∂₁ h (Flow₁ step₁ c))
                         (Flow₂ step₂ (GradedKernelHom₁.map∂₁ h c))

  open GradedKernelHomFlow₁ public

  fromGradedKernelHomFlow
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
      (h : GradedKernelHom₁ K₁ K₂)
    → KH.GradedKernelHomFlow K₁ K₂ (GradedKernelHom₁.hom h)
    → GradedKernelHomFlow₁ h
  fromGradedKernelHomFlow {K₁ = K₁} {K₂ = K₂} h hf =
    let
      module FH = GC.GradedFlowHom (KH.GradedKernelHomFlow.flow-hom hf)
      CP₂   = BulkBoundary.bnd (GradedKernel.BB K₂)
      step₁ = GradedKernel.step-grade K₁
      step₂ = GradedKernel.step-grade K₂
      Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
      map∂h = GradedKernelHom₁.map∂₁ h
      stepPres : ∀ c →
        ConPreorder._⊑_ CP₂ (map∂h (GradedClosure.Flow (GradedKernel.GTruth K₁) step₁ c))
                         (Flow₂ step₁ (map∂h c))
      stepPres c = FH.preserves-F step₁ c
      stepGrade : ∀ c → ConPreorder._⊑_ CP₂ (Flow₂ step₁ (map∂h c)) (Flow₂ step₂ (map∂h c))
      stepGrade c =
        GradedClosure.mono-grade (GradedKernel.GTruth K₂)
          (KH.GradedKernelHomFlow.step≤ hf)
          (map∂h c)
    in
    record
      { preserves-step = λ c → ConPreorder.trans CP₂ (stepPres c) (stepGrade c) }

  idGradedKernelHomFlow₁
    : ∀ (K : GradedKernel Sig Q)
    → GradedKernelHomFlow₁ (idGradedKernelHom₁ K)
  idGradedKernelHomFlow₁ K =
    let CP = BulkBoundary.bnd (GradedKernel.BB K) in
    record
      { preserves-step = λ _ → ConPreorder.refl CP }

  composeGradedKernelHomFlow₁
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {f : GradedKernelHom₁ K₁ K₂} {g : GradedKernelHom₁ K₂ K₃}
    → GradedKernelHomFlow₁ f
    → GradedKernelHomFlow₁ g
    → GradedKernelHomFlow₁ (g ∘₁ f)
  composeGradedKernelHomFlow₁ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f = f} {g = g} ff gg =
    let
      CP₃   = BulkBoundary.bnd (GradedKernel.BB K₃)
      Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)
      Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
      Flow₃ = GradedClosure.Flow (GradedKernel.GTruth K₃)
      step₁ = GradedKernel.step-grade K₁
      step₂ = GradedKernel.step-grade K₂
      step₃ = GradedKernel.step-grade K₃
      Th⋆₁  = GradedClosure.Th* (GradedKernel.GTruth K₁)
      Th⋆₂  = GradedClosure.Th* (GradedKernel.GTruth K₂)
      Th⋆₃  = GradedClosure.Th* (GradedKernel.GTruth K₃)
      mapf = GradedKernelHom₁.map∂₁ f
      mapg = GradedKernelHom₁.map∂₁ g
    in
    record
      { preserves-step = λ c →
          let
            stepA : ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                     (mapf (Flow₁ step₁ c))
                     (Flow₂ step₂ (mapf c))
            stepA = GradedKernelHomFlow₁.preserves-step ff c
            stepA' : ConPreorder._⊑_ CP₃ (mapg (mapf (Flow₁ step₁ c))) (mapg (Flow₂ step₂ (mapf c)))
            stepA' = GradedKernelHom₁.mono∂ g stepA
            stepB : ConPreorder._⊑_ CP₃ (mapg (Flow₂ step₂ (mapf c))) (Flow₃ step₃ (mapg (mapf c)))
            stepB = GradedKernelHomFlow₁.preserves-step gg (mapf c)
          in ConPreorder.trans CP₃ stepA' stepB
      }

  -- Flow-preserving 1-cells form a sub-2-category (same 2-cells, restricted 1-cells).

  module FlowSub₁ =
    FlowSub.With
      (GradedKernel Sig Q)
      GradedKernelHom₁
      GradedKernelHomFlow₁
      idGradedKernelHom₁
      composeGradedKernelHom₁
      idGradedKernelHomFlow₁
      composeGradedKernelHomFlow₁

  open FlowSub₁ public
    renaming
      ( Hom₁ᶠ        to GradedKernelHom₁ᶠ
      ; idHom₁ᶠ      to idGradedKernelHom₁ᶠ
      ; composeHom₁ᶠ to composeGradedKernelHom₁ᶠ
      )
