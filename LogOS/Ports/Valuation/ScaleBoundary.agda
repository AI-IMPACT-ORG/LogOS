{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.ScaleBoundary where

-- Scale/time boundaries induced by a `QAdapter`.
--
-- This is the bridge that lets kernels talk about numerics explicitly, without
-- baking valuation algebra into the v1.1 kernel core: equip a kernel with a
-- budget/time port into these boundaries, and require explicit transport
-- obligations on translations.

open import LogOS.Prelude using (Level)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Sup.FinSup using (FinSup)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter; QClock)

ScaleBoundary : ∀ {ℓ : Level} → QAdapter ℓ → ConPreorder ℓ ℓ
ScaleBoundary Q =
  record
    { Con = QAdapter.Scale Q
    ; _⊑_ = QAdapter._≤s_ Q
    ; refl = QAdapter.≤s-refl Q
    ; trans = QAdapter.≤s-trans Q
    }

-- The finite-join structure on the scale induces `FinSup` on the scale boundary.
--
-- This is the interface used by σ/ω-style iteration summaries (e.g. `run`) when
-- a `QAdapter` is used as the budget boundary.
ScaleBoundaryFinSup : ∀ {ℓ : Level} (Q : QAdapter ℓ) → FinSup (ScaleBoundary Q)
ScaleBoundaryFinSup Q =
  record
    { _⊔ᶠ_ = QAdapter._⊔s_ Q
    ; ⊥ᶠ = QAdapter.⊥s Q
    ; ⊥ᶠ-least = QAdapter.⊥s-least Q
    ; ⊔ᶠ-ub₁ = QAdapter.⊔s-ub₁ Q
    ; ⊔ᶠ-ub₂ = QAdapter.⊔s-ub₂ Q
    ; ⊔ᶠ-least = QAdapter.⊔s-least Q
    }

ProofBoundary : ∀ {ℓ : Level} → QAdapter ℓ → ConPreorder ℓ ℓ
ProofBoundary Q =
  record
    { Con = QAdapter.Scale Q
    ; _⊑_ = QAdapter._≤p_ Q
    ; refl = QAdapter.≤p-refl Q
    ; trans = QAdapter.≤p-trans Q
    }

-- A time preorder induced by the scale preorder via τ : Time → Scale.
--
-- This gives an explicit refinement notion on time “by cost/grade”.
TimeBoundary : ∀ {ℓ : Level} → (Q : QAdapter ℓ) → QClock Q → ConPreorder ℓ ℓ
TimeBoundary Q T =
  record
    { Con = QClock.Time T
    ; _⊑_ = λ t u → QAdapter._≤s_ Q (QClock.τ T t) (QClock.τ T u)
    ; refl = QAdapter.≤s-refl Q
    ; trans = QAdapter.≤s-trans Q
    }
