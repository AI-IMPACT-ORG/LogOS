{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.Textbook where

-- “ZFC in the flesh”, derived from the WFGraph route:
-- build a kernel + a textbook `ZFAxioms`/`ZFCAxioms` instance (full schemata),
-- with familiar names exposed via `SchemaTheorems`.
--
-- This module intentionally avoids the representability-by-codes upgrade used
-- by `FullUpgradeFromDefinable`: here we build the full schemata directly from
-- WFGraph `sup` formation (as a model construction step).

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel; kernelLike-fromKernel)

open import LogOS.Domain.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)
open import LogOS.Domain.ZFC.SetTheory.Pack as Pack using (ZFAxioms; ZFCAxioms)
open import LogOS.Domain.ZFC.SetTheory.FromZFAxioms using (toCumulativeHierarchy)
open import LogOS.Domain.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)
open import LogOS.Domain.ZFC.SetTheory.StageToCHFromHierarchy using (StageToCH-fromCH)
open import LogOS.Domain.ZFC.SetTheory.CumulativeSurface using (stageToSurface)
open import LogOS.Domain.ZFC.SetTheory.Dsl using (ZFDsl)
import LogOS.Domain.ZFC.SetTheory.Derived as Derived
import LogOS.Domain.ZFC.SetTheory.SchemaTheorems as Schema

open import LogOS.Domain.ZFC.WFGraph.Structure using (WFGraphStructure)
open import LogOS.Domain.ZFC.SetU.WFGraphCore using (WFGraph)
open import LogOS.Domain.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.Domain.ZFC.WFGraph.Model
  using (PowersetStructure; ExtensionalityStructure; FoundationStructure)
import LogOS.Domain.ZFC.WFGraph.ZFC as WFZFC

module ForZFC {ℓ : Level} (W : WFGraphStructure ℓ) where
  open WFGraphStructure W
  open WFGraph G renaming (Node to SetU; Edge to Edge)
  open SupStructure S renaming (supN to supNₛ; mem-sup↔ to mem-sup↔ₛ)

  module Base = WFZFC.ForZFC G S Ext P Fnd

  open Base public using (Sig; Q; K)

  open import LogOS.Domain.ZFC.SetTheory.DefinablePack using (ZFAxiomsᵈ)
  open ZFAxiomsᵈ Base.zfᵈ public
    using
      ( _∈_
      ; _≈_
      ; refl≈
      ; sym≈
      ; trans≈
      ; ⟦_⟧
      ; by-decode≈
      ; extensionality
      ; mem-ext
      ; empty
      ; pairing
      ; union
      ; powerset
      ; zeroS
      ; zeroS-empty
      ; succ
      ; mem-succ↔
      ; infinity
      ; foundation
      )

  -- Full (textbook) Separation/Replacement, constructed directly via `supN`.
  --
  -- This is a model-building step: `supN` is the only extra “collection”
  -- operator used here.

  separation
    : (P : SetU → Set ℓ)
    → ∀ x
    → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × (P z)))
  separation P x =
    supNₛ (Σ SetU (λ z → (z ∈ x) × P z)) proj₁
    , (λ z → intro (to z) (from z))
    where
      to : ∀ z → z ∈ supNₛ (Σ SetU (λ t → (t ∈ x) × P t)) proj₁ → (z ∈ x) × P z
      to z z∈ with _↔_.to (mem-sup↔ₛ {I = Σ SetU (λ t → (t ∈ x) × P t)} {f = proj₁} {y = z}) z∈
      ... | ((t , (t∈x , pt)) , eq) =
        subst (λ u → (u ∈ x) × P u) eq (t∈x , pt)

      from : ∀ z → (z ∈ x × P z) → z ∈ supNₛ (Σ SetU (λ t → (t ∈ x) × P t)) proj₁
      from z (z∈x , pz) =
        _↔_.from (mem-sup↔ₛ {I = Σ SetU (λ t → (t ∈ x) × P t)} {f = proj₁} {y = z})
          ((z , (z∈x , pz)) , refl)

  replacement
    : (F : SetU → Σ SetU (λ _ → Set ℓ))
    → ∀ x
    → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → u ∈ x × (proj₁ (F u) ≈ z))))
  replacement F x =
    supNₛ (Σ SetU (λ u → u ∈ x)) (λ { (u , _) → proj₁ (F u) })
    , (λ z → intro (to z) (from z))
    where
      to
        : ∀ z
        → z ∈ supNₛ (Σ SetU (λ u → u ∈ x)) (λ { (u , _) → proj₁ (F u) })
        → Σ SetU (λ u → u ∈ x × (proj₁ (F u) ≈ z))
      to z z∈ with _↔_.to (mem-sup↔ₛ {I = Σ SetU (λ u → u ∈ x)}
                                   {f = λ { (u , _) → proj₁ (F u) }}
                                   {y = z}) z∈
      ... | ((u , u∈x) , eq) = u , (u∈x , eq)

      from
        : ∀ z
        → (Σ SetU (λ u → u ∈ x × (proj₁ (F u) ≈ z)))
        → z ∈ supNₛ (Σ SetU (λ u → u ∈ x)) (λ { (u , _) → proj₁ (F u) })
      from z (u , (u∈x , img≡z)) =
        _↔_.from (mem-sup↔ₛ {I = Σ SetU (λ u0 → u0 ∈ x)}
                           {f = λ { (u0 , _) → proj₁ (F u0) }}
                           {y = z})
          ((u , u∈x) , img≡z)

  -- Textbook ZF axioms over the WFGraph kernel.
  zf : ZFAxioms (kernelLike-fromKernel K)
  zf =
    record
      { SetU   = SetU
      ; _∈_    = _∈_
      ; _≈_    = _≈_
      ; refl≈  = refl≈
      ; sym≈   = sym≈
      ; trans≈ = trans≈
      ; ⟦_⟧     = ⟦_⟧
      ; by-decode≈ = by-decode≈
      ; extensionality = extensionality
      ; mem-ext = mem-ext
      ; empty = empty
      ; pairing = pairing
      ; union  = union
      ; powerset = powerset
      ; zeroS = zeroS
      ; zeroS-empty = zeroS-empty
      ; succ  = succ
      ; mem-succ↔ = mem-succ↔
      ; infinity = infinity
      ; separation = separation
      ; replacement = replacement
      ; foundation = foundation
      }

  -- Staging/DSL: available for any `ZFAxioms` via the generic adapters.
  CH : CumulativeHierarchy K
  CH = toCumulativeHierarchy K zf

  stageToCH = StageToCH-fromCH K CH

  surface : ZFDsl K
  surface = stageToSurface K stageToCH

  -- Set-theorist friendly names and small derived constructors.
  module ZFTextbook = Schema.ZF K zf
  open ZFTextbook public hiding (SetU; _∈_; _≈_; refl≈; sym≈; trans≈; separation; replacement)

  singleton : SetU → SetU
  singleton = Derived.singleton (kernelLike-fromKernel K) zf

  mem-singleton↔ : ∀ {x z} → (z ∈ singleton x) ↔ (z ≈ x)
  mem-singleton↔ = Derived.mem-singleton↔ (kernelLike-fromKernel K) zf

  union₂ : SetU → SetU → SetU
  union₂ = Derived.union₂ (kernelLike-fromKernel K) zf

  mem-union₂↔ : ∀ {x y z} → (z ∈ union₂ x y) ↔ ((z ∈ x) ⊎ (z ∈ y))
  mem-union₂↔ = Derived.mem-union₂↔ (kernelLike-fromKernel K) zf

  module WithChoice
    (choice : AxiomOfChoice (ZFAxioms.SetU zf) (ZFAxioms._∈_ zf) (ZFAxioms._≈_ zf) (ZFAxioms.pairing zf))
    where
    zfc : ZFCAxioms (kernelLike-fromKernel K)
    zfc = record { zf = zf ; AC = choice }

    module ZFCTextbook = Schema.ZFC K zfc
    open ZFCTextbook public hiding (separation; replacement)
