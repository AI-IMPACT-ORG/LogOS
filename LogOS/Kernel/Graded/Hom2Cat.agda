{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Hom2Cat where

-- 2-categorical “refinement” view on graded-kernel morphisms.
--
-- Implementation note: the 2-cell calculus is defined once for the CHL-facing
-- `LogicKernel` interface (`LogOS.Kernel.LogicKernel.Hom2Cat`). This module is
-- a thin wrapper that:
-- - embeds graded kernels via `FromGradedKernel.asLogicKernel`;
-- - reuses the `LogicKernel` 2-cell calculus by translating 1-cells.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Algebra.ConAlg using (ConAlgHom≡)
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)

open import LogOS.Kernel.Graded
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFrom
open import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub
import LogOS.Kernel.Graded.Hom as KH
import LogOS.Kernel.LogicKernel.Hom as LKH
import LogOS.Kernel.LogicKernel.Hom2Cat as LK2

private
  module GC = Truth.GuardedCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    asLK : GradedKernel Sig Q → LogicKernel Sig Q
    asLK = LKFrom.asLogicKernel

    toLKHom
      : ∀ {K₁ K₂ : GradedKernel Sig Q}
      → KH.GradedKernelHom K₁ K₂ → LKH.LogicKernelHom (asLK K₁) (asLK K₂)
    toLKHom h = record
      { con-hom    = KH.GradedKernelHom.con-hom h
      ; mapCode    = KH.GradedKernelHom.mapCode h
      ; map-encode = KH.GradedKernelHom.map-encode h
      ; map-decode = KH.GradedKernelHom.map-decode h
      }

    fromLKHom
      : ∀ {K₁ K₂ : GradedKernel Sig Q}
      → LKH.LogicKernelHom (asLK K₁) (asLK K₂) → KH.GradedKernelHom K₁ K₂
    fromLKHom h = record
      { con-hom    = LKH.LogicKernelHom.con-hom h
      ; mapCode    = LKH.LogicKernelHom.mapCode h
      ; map-encode = LKH.LogicKernelHom.map-encode h
      ; map-decode = LKH.LogicKernelHom.map-decode h
      }

  record GradedKernelHom₁ (K₁ K₂ : GradedKernel Sig Q) : Set (lsuc (lsuc ℓ)) where
    private
      CP₁ = BulkBoundary.bnd (GradedKernel.BB K₁)
      CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
    field
      hom   : KH.GradedKernelHom K₁ K₂
      mono∂ :
        ∀ {c c'}
        → ConPoset._⊑_ CP₁ c c'
        → ConPoset._⊑_ CP₂ (ConAlgHom≡.map∂ (KH.GradedKernelHom.con-hom hom) c)
                           (ConAlgHom≡.map∂ (KH.GradedKernelHom.con-hom hom) c')

    map∂₁ : ConPoset.Con CP₁ → ConPoset.Con CP₂
    map∂₁ = ConAlgHom≡.map∂ (KH.GradedKernelHom.con-hom hom)

    mapCode₁ : GradedKernel.Code K₁ → GradedKernel.Code K₂
    mapCode₁ = KH.GradedKernelHom.mapCode hom

    map-decode₁ : ∀ γ → GradedKernel.decode K₂ (mapCode₁ γ) ≡ map∂₁ (GradedKernel.decode K₁ γ)
    map-decode₁ = KH.GradedKernelHom.map-decode hom

  open GradedKernelHom₁ public

  toLKHom₁
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → LK2.LogicKernelHom₁ (asLK K₁) (asLK K₂)
  toLKHom₁ h =
    record
      { hom   = toLKHom (GradedKernelHom₁.hom h)
      ; mono∂ = GradedKernelHom₁.mono∂ h
      }

  fromLKHom₁
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → LK2.LogicKernelHom₁ (asLK K₁) (asLK K₂) → GradedKernelHom₁ K₁ K₂
  fromLKHom₁ h =
    record
      { hom   = fromLKHom (LK2.LogicKernelHom₁.hom h)
      ; mono∂ = LK2.LogicKernelHom₁.mono∂ h
      }

  idGradedKernelHom₁ : ∀ (K : GradedKernel Sig Q) → GradedKernelHom₁ K K
  idGradedKernelHom₁ K = fromLKHom₁ (LK2.idLogicKernelHom₁ (asLK K))

  composeGradedKernelHom₁
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₂ K₃ → GradedKernelHom₁ K₁ K₃
  composeGradedKernelHom₁ f g =
    fromLKHom₁ (LK2.composeLogicKernelHom₁ (toLKHom₁ f) (toLKHom₁ g))

  infixr 9 _∘₁_
  _∘₁_
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₂ K₃ → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₃
  g ∘₁ f = composeGradedKernelHom₁ f g

  -- 2-cells: reuse the `LogicKernel` calculus after translating 1-cells.

  infix 4 _⇒_
  _⇒_
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₂ → Set ℓ
  f ⇒ g = LK2._⇒_ (toLKHom₁ f) (toLKHom₁ g)

  refl⇒ : ∀ {K₁ K₂ : GradedKernel Sig Q} (f : GradedKernelHom₁ K₁ K₂) → f ⇒ f
  refl⇒ f = LK2.refl⇒ (toLKHom₁ f)

  trans⇒
    : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g h : GradedKernelHom₁ K₁ K₂}
    → f ⇒ g → g ⇒ h → f ⇒ h
  trans⇒ {f = f} {g = g} {h = h} fg gh =
    LK2.trans⇒ {f = toLKHom₁ f} {g = toLKHom₁ g} {h = toLKHom₁ h} fg gh

  whiskerR
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {g g' : GradedKernelHom₁ K₂ K₃}
      (f : GradedKernelHom₁ K₁ K₂)
    → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f)
  whiskerR {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg' =
    LK2.whiskerR
      {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃}
      {g = toLKHom₁ g} {g' = toLKHom₁ g'}
      (toLKHom₁ f)
      gg'

  whiskerL
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      (g : GradedKernelHom₁ K₂ K₃)
      {f f' : GradedKernelHom₁ K₁ K₂}
    → f ⇒ f' → (g ∘₁ f) ⇒ (g ∘₁ f')
  whiskerL {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff' =
    LK2.whiskerL
      {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃}
      (toLKHom₁ g)
      {f = toLKHom₁ f} {f' = toLKHom₁ f'}
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

  GradedKernelHomPoset
    : GradedKernel Sig Q → GradedKernel Sig Q → ConPoset (lsuc (lsuc ℓ))
  GradedKernelHomPoset K₁ K₂ =
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
      ; Hom = GradedKernelHomPoset
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
          ( lift (LK2.id-left⇒ {K₁ = asLK A} {K₂ = asLK B} (toLKHom₁ f))
          , lift (LK2.id-left⇐ {K₁ = asLK A} {K₂ = asLK B} (toLKHom₁ f))
          )
      ; id-right = λ {A} {B} f →
          ( lift (LK2.id-right⇒ {K₁ = asLK A} {K₂ = asLK B} (toLKHom₁ f))
          , lift (LK2.id-right⇐ {K₁ = asLK A} {K₂ = asLK B} (toLKHom₁ f))
          )
      ; assoc = λ {A} {B} {C} {D} f g h →
          ( lift (LK2.assoc⇒ {K₁ = asLK A} {K₂ = asLK B} {K₃ = asLK C} {K₄ = asLK D}
                    (toLKHom₁ h) (toLKHom₁ g) (toLKHom₁ f))
          , lift (LK2.assoc⇐ {K₁ = asLK A} {K₂ = asLK B} {K₃ = asLK C} {K₄ = asLK D}
                    (toLKHom₁ h) (toLKHom₁ g) (toLKHom₁ f))
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
      {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃}
      {f = toLKHom₁ f} {f' = toLKHom₁ f'} {g = toLKHom₁ g} {g' = toLKHom₁ g'}
      ff'
      gg'

  -- Observational equivalence: mutual refinement.

  infix 4 _≈_
  _≈_
    : ∀ {K₁ K₂ : GradedKernel Sig Q}
    → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₂ → Set ℓ
  f ≈ g = LK2._≈_ (toLKHom₁ f) (toLKHom₁ g)

  refl≈ : ∀ {K₁ K₂ : GradedKernel Sig Q} (f : GradedKernelHom₁ K₁ K₂) → f ≈ f
  refl≈ f = LK2.refl≈ (toLKHom₁ f)

  sym≈ : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g : GradedKernelHom₁ K₁ K₂} → f ≈ g → g ≈ f
  sym≈ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} fg =
    LK2.sym≈ {K₁ = asLK K₁} {K₂ = asLK K₂} {f = toLKHom₁ f} {g = toLKHom₁ g} fg

  trans≈
    : ∀ {K₁ K₂ : GradedKernel Sig Q} {f g h : GradedKernelHom₁ K₁ K₂}
    → f ≈ g → g ≈ h → f ≈ h
  trans≈ {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} {h = h} fg gh =
    LK2.trans≈ {K₁ = asLK K₁} {K₂ = asLK K₂} {f = toLKHom₁ f} {g = toLKHom₁ g} {h = toLKHom₁ h} fg gh

  cong-∘₁-≈
    : ∀ {K₁ K₂ K₃ : GradedKernel Sig Q}
      {f f' : GradedKernelHom₁ K₁ K₂}
      {g g' : GradedKernelHom₁ K₂ K₃}
    → f ≈ f'
    → g ≈ g'
    → (g ∘₁ f) ≈ (g' ∘₁ f')
  cong-∘₁-≈ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff gg =
    LK2.cong-∘₁-≈
      {K₁ = asLK K₁} {K₂ = asLK K₂} {K₃ = asLK K₃}
      {f = toLKHom₁ f} {f' = toLKHom₁ f'} {g = toLKHom₁ g} {g' = toLKHom₁ g'}
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
      Th⋆₁  = GradedClosure.Th* (GradedKernel.GTruth K₁)
      Th⋆₂  = GradedClosure.Th* (GradedKernel.GTruth K₂)
    field
      preserves-step : ∀ c →
        ConPoset._⊑_ CP₂ (GradedKernelHom₁.map∂₁ h (Flow₁ step₁ c))
                         (Flow₂ step₂ (GradedKernelHom₁.map∂₁ h c))
      preserves-Th   : ConPoset._⊑_ CP₂ (GradedKernelHom₁.map∂₁ h Th⋆₁) Th⋆₂

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
        ConPoset._⊑_ CP₂ (map∂h (GradedClosure.Flow (GradedKernel.GTruth K₁) step₁ c))
                         (Flow₂ step₁ (map∂h c))
      stepPres c = FH.preserves-F step₁ c
      stepGrade : ∀ c → ConPoset._⊑_ CP₂ (Flow₂ step₁ (map∂h c)) (Flow₂ step₂ (map∂h c))
      stepGrade c =
        GradedClosure.mono-grade (GradedKernel.GTruth K₂)
          (KH.GradedKernelHomFlow.step≤ hf)
          (map∂h c)
    in
    record
      { preserves-step = λ c → ConPoset.trans CP₂ (stepPres c) (stepGrade c)
      ; preserves-Th   = FH.preserves-Th
      }

  idGradedKernelHomFlow₁
    : ∀ (K : GradedKernel Sig Q)
    → GradedKernelHomFlow₁ (idGradedKernelHom₁ K)
  idGradedKernelHomFlow₁ K =
    let CP = BulkBoundary.bnd (GradedKernel.BB K) in
    record
      { preserves-step = λ _ → ConPoset.refl CP
      ; preserves-Th   = ConPoset.refl CP
      }

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
            stepA : ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                     (mapf (Flow₁ step₁ c))
                     (Flow₂ step₂ (mapf c))
            stepA = GradedKernelHomFlow₁.preserves-step ff c
            stepA' : ConPoset._⊑_ CP₃ (mapg (mapf (Flow₁ step₁ c))) (mapg (Flow₂ step₂ (mapf c)))
            stepA' = GradedKernelHom₁.mono∂ g stepA
            stepB : ConPoset._⊑_ CP₃ (mapg (Flow₂ step₂ (mapf c))) (Flow₃ step₃ (mapg (mapf c)))
            stepB = GradedKernelHomFlow₁.preserves-step gg (mapf c)
          in ConPoset.trans CP₃ stepA' stepB
      ; preserves-Th =
          let
            stepA : ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂)) (mapf Th⋆₁) Th⋆₂
            stepA = GradedKernelHomFlow₁.preserves-Th ff
            stepA' : ConPoset._⊑_ CP₃ (mapg (mapf Th⋆₁)) (mapg Th⋆₂)
            stepA' = GradedKernelHom₁.mono∂ g stepA
            stepB : ConPoset._⊑_ CP₃ (mapg Th⋆₂) Th⋆₃
            stepB = GradedKernelHomFlow₁.preserves-Th gg
          in ConPoset.trans CP₃ stepA' stepB
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
