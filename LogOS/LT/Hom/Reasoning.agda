{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Hom.Reasoning where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Reasoning combinators for observational refinements on kernel morphisms.
--
-- LogOS exposes two equivalent pullback refinements:
--
-- - boundary-driven (base `LOG`): `_⇒∂_` (pullback along `transportView`)
-- - implementation-first: `_⇒_` (pullback along `obsView`)
--
-- This module exposes the standard preorder reasoning combinators with names
-- that read as adapter refinement chains (both flavours):
--
--   begin⇒∂
--     f ⇒∂⟨ fg ⟩
--     g ⇒∂⟨ gh ⟩
--     h ∎⇒∂
--
--   begin⇒
--     f ⇒⟨ fg ⟩
--     g ⇒⟨ gh ⟩
--     h ∎⇒

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (obsView; transportView)
open import LogOS.LT.View using (PullbackPreorder)
open import LogOS.LT.View.Roles using (forget)

module ImplementationReasoning
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  where

  private
    CP : ConPreorder _ _
    CP = PullbackPreorder (forget (obsView {K = K} {K' = K'}))

  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R renaming
    ( begin⊑_ to begin⇒_
    ; _⊑⟨_⟩_ to _⇒⟨_⟩_
    ; _∎⊑ to _∎⇒
    )

module HomReasoning
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  where

  private
    CP : ConPreorder _ _
    CP = PullbackPreorder (forget (transportView {K = K} {K' = K'}))

  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R renaming
    ( begin⊑_ to begin⇒∂_
    ; _⊑⟨_⟩_ to _⇒∂⟨_⟩_
    ; _∎⊑ to _∎⇒∂
    )
