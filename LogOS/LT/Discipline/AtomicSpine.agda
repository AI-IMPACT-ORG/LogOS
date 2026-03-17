{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Discipline.AtomicSpine where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Atomic spine discipline gates.
--
-- This module is intentionally brittle: it asserts that the core “explains
-- itself” definitionally by building each layer as a categorical construction
-- over the previous one (views/pullbacks, observational refinement, etc.).

open import LogOS.Prelude using (Level; lzero; _⊔_; ⊤; tt; _≡_; refl)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (PullbackPreorder; _⊑[_]_)
open import LogOS.LT.View.Roles using (forget)
open import LogOS.LT.Kernel using (Kernel; decodeView; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; transportView; _⇒∂_)

private
  -- Kernel: code refinement is definitionally a pullback along `decode`.
  CodePreorder-def
    : ∀ {ℓ ℓRel ℓCode : Level}
    → (K : Kernel ℓ ℓRel ℓCode)
    → CodePreorder K ≡ PullbackPreorder (forget (decodeView K))
  CodePreorder-def _ = refl

  -- Hom: canonical 2-cells/refinement are definitionally a pullback along
  -- `transportView` (what the observer sees transported by `map∂`).
  ⇒∂-def
    : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {K' : Kernel ℓ ℓRel ℓCode'}
    → (f g : KernelHom K K')
    → (f ⇒∂ g) ≡ (f ⊑[ forget (transportView {K = K} {K' = K'}) ] g)
  ⇒∂-def _ _ = refl

-- Export one harmless witness so this module can be imported via the API
-- without re-exporting all internal discipline lemmas.
ok : ⊤ {ℓ = lzero}
ok = tt
