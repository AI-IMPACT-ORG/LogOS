{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.CriticalParameter where

-- Critical parameters / sharp thresholds (refinement-first, minimal).
--
-- This module is *not* number theory, complexity theory, or physics.
-- It is a small structural vocabulary that captures a recurring theorem shape:
--
-- - there is a parameter preorder `T` (time/scale/budget/noise/…),
-- - there is a monotone predicate `Good : T → Set` (“good region” is upward closed),
-- - and one exhibits a least cutpoint `Λ` such that `Good` holds for all parameters above `Λ`.
--
-- Reading examples:
-- - de Bruijn–Newman: `Good t` = “Ξₜ has only real zeros”, `Λ` = Newman constant.
-- - Budgets: `Good B` = “a spec holds within budget B”, `Λ` = minimal required budget.
-- - Noise/privacy: `Good ε` = “indistinguishable at level ε”, `Λ` = minimal noise level.
--
-- All domain content lives in the choice of `T` and `Good` (and any proof that
-- `Good` is monotone). This module only packages the *obligation shape*.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)

module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- Upward closure of a predicate with respect to a parameter preorder.
UpClosed
  : ∀ {ℓCon ℓRel ℓP : Level}
  → (T : ConPreorder ℓCon ℓRel)
  → (Good : Con T → Set ℓP)
  → Set (ℓCon ⊔ ℓRel ⊔ ℓP)
UpClosed T Good = ∀ {t u} → _⊑_ T t u → Good t → Good u

-- Strict refinement (for “fails below Λ” statements).
--
-- This is *not* antisymmetry: it is the preorder-level strict relation
-- “t refines u, but u does not refine t”.
infix 4 _≺_
_≺_
  : ∀ {ℓCon ℓRel : Level}
  → (T : ConPreorder ℓCon ℓRel)
  → Con T → Con T → Set ℓRel
_≺_ T t u = (_⊑_ T t u) × ¬ (_⊑_ T u t)

-- Least cutpoint / “critical parameter” for a monotone `Good`.
--
-- `GoodAbove`: `Good` holds for all parameters above `Λ`.
-- `least`: any other cutpoint is above `Λ`.
record CriticalCut
  {ℓCon ℓRel ℓP : Level}
  (T : ConPreorder ℓCon ℓRel)
  (Good : Con T → Set ℓP)
  : Set (lsuc (ℓCon ⊔ ℓRel ⊔ ℓP)) where
  field
    good-mono : UpClosed T Good

    Λ : Con T

    GoodAbove
      : ∀ {t}
      → _⊑_ T Λ t
      → Good t

    least
      : ∀ {cut}
      → (∀ {t} → _⊑_ T cut t → Good t)
      → _⊑_ T Λ cut

open CriticalCut public

principalCut
  : ∀ {ℓCon ℓRel}
    (T : ConPreorder ℓCon ℓRel)
    (Λ₀ : Con T)
  → CriticalCut T (λ t → _⊑_ T Λ₀ t)
principalCut T Λ₀ =
  let
    module R = ≤-Reasoning T
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  record
    { good-mono = λ t≤u Λ≤t →
        begin⊑
          Λ₀
            ⊑⟨ Λ≤t ⟩
          _
            ⊑⟨ t≤u ⟩
          _
        ∎⊑
    ; Λ = Λ₀
    ; GoodAbove = λ Λ≤t → Λ≤t
    ; least = λ cutGood → cutGood (ConPreorder.refl T)
    }

-- Derived: any “good” parameter lies above the cutpoint.
Λ≤Good
  : ∀ {ℓCon ℓRel ℓP : Level}
    {T : ConPreorder ℓCon ℓRel}
    {Good : Con T → Set ℓP}
  → (C : CriticalCut T Good)
  → ∀ {t}
  → Good t
  → _⊑_ T (Λ C) t
Λ≤Good {T = T} C {t} goodt =
  least C (λ {u} t≤u → good-mono C t≤u goodt)

-- Optional strengthening: the cutpoint is sharp (“everything strictly below fails”).
record SharpCut
  {ℓCon ℓRel ℓP : Level}
  (T : ConPreorder ℓCon ℓRel)
  (Good : Con T → Set ℓP)
  : Set (lsuc (ℓCon ⊔ ℓRel ⊔ ℓP)) where
  field
    base : CriticalCut T Good

    belowFails
      : ∀ {t}
      → _≺_ T t (Λ base)
      → ¬ Good t

open SharpCut public

principalSharpCut
  : ∀ {ℓCon ℓRel}
    (T : ConPreorder ℓCon ℓRel)
    (Λ₀ : Con T)
  → SharpCut T (λ t → _⊑_ T Λ₀ t)
principalSharpCut T Λ₀ =
  record
    { base = principalCut T Λ₀
    ; belowFails = λ {t} (_ , t⋠Λ₀) → t⋠Λ₀
    }
