{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.Regularisation where

-- Regularisation vocabulary for valuation boundaries (refinement-first).
--
-- QFT reading:
-- - regularisation evaluates into a boundary where “singular structure” is visible
--   (e.g. Laurent series in epsilon), and
-- - a subtraction scheme is captured by a split/projection into “pole part” and
--   “finite part” (normalisation conditions can then be imposed on the finite part).
--
-- LogOS keeps only the categorical shadow:
-- - no subtraction,
-- - no linear structure,
-- - laws are stated at the refinement level (`⊑`, `≈`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder; Con; _⊑_; _≈_; MonoOn; refl⊑ )
open import LogOS.LT.Sup.FinSup using (FinSup)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)

-- Optional strengthening: additive bottom is a multiplicative zero.
--
-- This is the property needed for “series-like” constructors (units with
-- zero coefficients, pole/finite ideals, etc.). It is intentionally not baked
-- into `JoinPrequantale`.
record HasMulZero {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  (JP : JoinPrequantale CP)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  open JoinPrequantale JP
  open FinSup FS
  field
    botMulZero : ∀ a → _⊑_ CP (⊥ᶠ · a) ⊥ᶠ
    mulBotZero : ∀ a → _⊑_ CP (a · ⊥ᶠ) ⊥ᶠ

  botMulZeroEq : ∀ a → _≈_ CP (⊥ᶠ · a) ⊥ᶠ
  botMulZeroEq a = (botMulZero a , ⊥ᶠ-least (⊥ᶠ · a))

  mulBotZeroEq : ∀ a → _≈_ CP (a · ⊥ᶠ) ⊥ᶠ
  mulBotZeroEq a = (mulBotZero a , ⊥ᶠ-least (a · ⊥ᶠ))

open HasMulZero public
-- Pole/finite split on a join-prequantale boundary.
--
-- This is the refinement-first analogue of a minimal-subtraction projector
-- (pole extraction) and its complement (finite part).
record PoleSplit {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  (JP : JoinPrequantale CP)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  open JoinPrequantale JP
  open FinSup FS
  field
    pole   : Con CP → Con CP
    finite : Con CP → Con CP

    pole-mono   : MonoOn CP pole
    finite-mono : MonoOn CP finite

    pole-idem≈   : ∀ a → _≈_ CP (pole (pole a)) (pole a)
    finite-idem≈ : ∀ a → _≈_ CP (finite (finite a)) (finite a)

    -- Decomposition axiom: the regularised value is the (finite) join of its
    -- pole and finite parts, up to mutual refinement.
    split≈ : ∀ a → _≈_ CP a (pole a ⊔ᶠ finite a)

open PoleSplit public
