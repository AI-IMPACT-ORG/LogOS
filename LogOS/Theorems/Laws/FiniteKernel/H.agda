{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Laws.FiniteKernel.H where

-- Free constraint algebra fold preservation and completeness.
-- Proven from the initial/free construction with no additional postulates.

open import LogOS.Prelude
open import LogOS.Algebra.ConAlg
open import LogOS.Free.Constraints

-- Fold from the free constraint algebra preserves generated preorders.

fold∂-preserves
  : ∀ {ℓ} (A : ConAlg {ℓ}) {x y : Con∂}
  → x ≤∂ y → ConAlg._⊑bnd_ A (interp∂ A x) (interp∂ A y)
fold∂-preserves A p = interp∂-mono A p

foldb-preserves
  : ∀ {ℓ} (A : ConAlg {ℓ}) {x y : Conb}
  → x ≤b y → ConAlg._⊑bulk_ A (interpb A x) (interpb A y)
foldb-preserves A p = interpb-mono A p

-- Completeness schema: if an inequality holds under every strict fold
-- into any model, it holds in the free algebra (choose id on Free).

complete∂
  : ∀ {ℓ} {x y : Con∂}
  → (∀ (A : ConAlg {ℓ}) (h : ConAlgHom≡ FreeConAlg A) →
       ConAlg._⊑bnd_ A (ConAlgHom≡.map∂ h x) (ConAlgHom≡.map∂ h y))
  → x ≤∂ y
complete∂ hyp = hyp FreeConAlg (idHom≡ FreeConAlg)

completeb
  : ∀ {ℓ} {x y : Conb}
  → (∀ (A : ConAlg {ℓ}) (h : ConAlgHom≡ FreeConAlg A) →
       ConAlg._⊑bulk_ A (ConAlgHom≡.mapb h x) (ConAlgHom≡.mapb h y))
  → x ≤b y
completeb hyp = hyp FreeConAlg (idHom≡ FreeConAlg)
