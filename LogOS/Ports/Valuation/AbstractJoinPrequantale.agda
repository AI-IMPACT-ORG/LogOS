{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.AbstractJoinPrequantale where

-- Join-prequantale vocabulary for valuation boundaries (refinement-first).
--
-- The design-target spec treats valuation algebra as an *optional* layer: kernels
-- stay refinement-first and decode-extensional, and numerics enter only through
-- explicit ports/adapters.
--
-- The key discipline point here is the law level:
-- join-prequantale laws are stated up to mutual refinement (`≈`), not `≡`.
-- (Strict `≡` laws can be used as an implementation convenience, but are not
-- the intended semantic equality.)
--
-- Finite joins only: this is a finite-join prequantale, not a complete quantale.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; ≡→≈)
open import LogOS.LT.Sup.FinSup using (FinSup)

open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary; ScaleBoundaryFinSup)

record JoinPrequantale {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  infixl 7 _·_
  field
    FS : FinSup CP

    _·_ : Con CP → Con CP → Con CP
    e   : Con CP

    ·-mono : ∀ {a b c d} → _⊑_ CP a b → _⊑_ CP c d → _⊑_ CP (a · c) (b · d)

    ·-assoc≈ : ∀ a b c → _≈_ CP ((a · b) · c) (a · (b · c))
    ·-idl≈   : ∀ a → _≈_ CP (e · a) a
    ·-idr≈   : ∀ a → _≈_ CP (a · e) a

    ·-distl-⊔ᶠ≈
      : ∀ a b c
      → _≈_ CP ((FinSup._⊔ᶠ_ FS a b) · c)
               (FinSup._⊔ᶠ_ FS (a · c) (b · c))

    ·-distr-⊔ᶠ≈
      : ∀ a b c
      → _≈_ CP (a · (FinSup._⊔ᶠ_ FS b c))
               (FinSup._⊔ᶠ_ FS (a · b) (a · c))

open JoinPrequantale public
-- Any `QAdapter` yields a join-prequantale structure on its induced scale boundary.
--
-- This is “cheap”: it uses no extra axioms, and converts strict `≡` laws from the
-- adapter into the refinement-first law level (`≈`) expected downstream.
ScaleJoinPrequantale : ∀ {ℓQ : Level} (Q : QAdapter ℓQ) → JoinPrequantale (ScaleBoundary Q)
ScaleJoinPrequantale Q =
  record
    { FS = ScaleBoundaryFinSup Q
    ; _·_ = QAdapter._·_ Q
    ; e   = QAdapter.e Q
    ; ·-mono = QAdapter.·-mono Q
    ; ·-assoc≈ = λ a b c → ≡→≈ {CP = ScaleBoundary Q} (QAdapter.·-assoc Q a b c)
    ; ·-idl≈   = λ a → ≡→≈ {CP = ScaleBoundary Q} (QAdapter.·-idl Q a)
    ; ·-idr≈   = λ a → ≡→≈ {CP = ScaleBoundary Q} (QAdapter.·-idr Q a)
    ; ·-distl-⊔ᶠ≈ = λ a b c → ≡→≈ {CP = ScaleBoundary Q} (QAdapter.·-distl-⊔s Q a b c)
    ; ·-distr-⊔ᶠ≈ = λ a b c → ≡→≈ {CP = ScaleBoundary Q} (QAdapter.·-distr-⊔s Q a b c)
    }
