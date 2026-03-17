{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.PresentationAdapters where

-- Canonical refinement-first LT presentation adapters for the raw iterative
-- tree presentation. This packages the strict-to-refined bridge once, so the
-- ZFC model code consumes the canonical LT contracts directly.

open import LogOS.Prelude

import LogOS.LT.Presentation.GeneratedImage as GenImage
import LogOS.LT.Presentation.GeneratedSubobject.Core as GenSub

import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST
import LogOS.Apps.ZFC.Models.IterativeSetTree.Context as Ctx
import LogOS.Apps.ZFC.Models.IterativeSetTree.GeneratedImage as Image
import LogOS.Apps.ZFC.Models.IterativeSetTree.GeneratedSubtree as Subtree
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

module For {ℓ : Level} (collapse : Stage.ExtensionalCollapseᵛ {ℓ}) where
  open Stage.ExtensionalCollapseᵛ collapse using (extensionalityᵛ)

  private
    C : ZF.SetContext {lsuc ℓ}
    C = Ctx.ctxᵛ {ℓ}

  module Mem = ZF.SetContext C

  localGeneratorsᵛ : GenSub.LocalGenerators (IST.V {ℓ}) IST._∈ᵛ_ Mem._≈_ ℓ
  localGeneratorsᵛ =
    GenSub.strictLocalGenerators
      (Subtree.strictLocalGeneratorsᵛ {ℓ})
      Mem._≈_
      extensionalityᵛ
      Mem.≡→≈

  generatedSubtreesᵛ : GenSub.GeneratedSubobjects localGeneratorsᵛ ℓ
  generatedSubtreesᵛ =
    GenSub.strictGeneratedSubobjects
      localGeneratorsᵛ
      (Subtree.strictGeneratedSubtreesᵛ {ℓ})
      extensionalityᵛ
      Mem.≡→≈

  generatedImagesᵛ : GenImage.GeneratedImages localGeneratorsᵛ
  generatedImagesᵛ =
    GenImage.strictGeneratedImages
      localGeneratorsᵛ
      (Image.strictGeneratedImagesᵛ {ℓ})
      extensionalityᵛ
      Mem.≡→≈

module LiftedFor {ℓ : Level} (collapse : Stage.ExtensionalCollapseᵛ {lsuc ℓ}) where
  open Stage.ExtensionalCollapseᵛ collapse using (extensionalityᵛ)

  private
    C₁ : ZF.SetContext {lsuc (lsuc ℓ)}
    C₁ = Ctx.ctxᵛ {lsuc ℓ}

  module Mem₁ = ZF.SetContext C₁

  liftedFilterMemberIn
    : (liftᵛ : IST.V {ℓ} → IST.V {lsuc ℓ})
    → (liftIdx : (x : IST.V {ℓ}) → IST.Idx x → IST.Idx (liftᵛ x))
    → (elemAt-lift : ∀ (x : IST.V {ℓ}) → (i : IST.Idx x) → IST.elemAt (liftᵛ x) (liftIdx x i) ≡ liftᵛ (IST.elemAt x i))
    → (liftPreserves≈ : ∀ {x y : IST.V {ℓ}} → ZF.SetContext._≈_ (Ctx.ctxᵛ {ℓ}) x y → Mem₁._≈_ (liftᵛ x) (liftᵛ y))
    → {x z : IST.V {ℓ}}
    → (Q : IST.Idx (liftᵛ x) → Set (lsuc ℓ))
    → (i : IST.Idx x)
    → Q (liftIdx x i)
    → ZF.SetContext._≈_ (Ctx.ctxᵛ {ℓ}) z (IST.elemAt x i)
    → liftᵛ z IST.∈ᵛ Subtree.filterᵛ (liftᵛ x) Q
  liftedFilterMemberIn liftᵛ liftIdx elemAt-lift liftPreserves≈ {x} {z} Q i qi z≈child =
    Subtree.filter-memberIn Q (liftIdx x i) qi liftz≡child
    where
      liftz≡child : liftᵛ z ≡ IST.elemAt (liftᵛ x) (liftIdx x i)
      liftz≡child =
        extensionalityᵛ
          (Mem₁.trans≈
            (liftPreserves≈ z≈child)
            (Mem₁.≡→≈ (sym (elemAt-lift x i))))
