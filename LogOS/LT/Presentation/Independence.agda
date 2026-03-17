{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.Independence where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Presentation independence (kernel discipline).
--
-- Once a view `V` is fixed, any *complete* presentation for `V` is equivalent
-- to the canonical pullback refinement along `V`. Therefore any two complete
-- presentations for the same view are equivalent: the presentation does not
-- change meaning, it only provides a particular derivation interface.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ↔-sym; ↔-trans)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (View)
open import LogOS.LT.Presentation using
  ( Presentation
  ; CompletePresentation
  ; presentation↔canonical
  )

presentationsAgree
  : ∀ {ℓX ℓR₁ ℓR₂ ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    {V : View X O}
  → (P : Presentation {ℓR = ℓR₁} V)
  → (Q : Presentation {ℓR = ℓR₂} V)
  → CompletePresentation P
  → CompletePresentation Q
  → ∀ {x y}
  → (Presentation._≼_ P x y) ↔ (Presentation._≼_ Q x y)
presentationsAgree P Q CP CQ =
  ↔-trans
    (presentation↔canonical P CP)
    (↔-sym (presentation↔canonical Q CQ))
