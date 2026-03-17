{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.AbstractQuanticNucleus where

-- Quantic nuclei on valuation boundaries (refinement-first).
--
-- A quantic nucleus is a guarded closure (`Flow`) that additionally preserves
-- the join-prequantale structure (finite joins, not arbitrary joins).
--
-- In particular:
-- - finite joins are preserved up to mutual refinement (`≈`), and
-- - multiplication is preserved *laxly* (nucleus-style):
--
--     Flow a · Flow b ⊑ Flow (a · b)
--
-- This keeps the layer weak/general: stable points need not be closed under the
-- raw multiplication, but they are closed under the *reflected* multiplication
-- `x ⊙ y = Flow (x · y)`.
--
-- This module is intentionally minimal: it does not assume any completeness
-- beyond finite joins (those are part of `JoinPrequantale`).

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.List.Ops using (_∈_; here; there)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; mkStable; elem; stable)
open import LogOS.LT.Sup.FinSup using (FinSup)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)

record QuanticNucleus {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  (JP : JoinPrequantale CP)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  open JoinPrequantale JP
  open FinSup FS
  field
    GC : GuardedClosure CP

    preserves-⊔ᶠ≈
      : ∀ a b
      → _≈_ CP
          (Flow GC (a ⊔ᶠ b))
          (Flow GC a ⊔ᶠ Flow GC b)

    lax-·
      : ∀ a b
      → _⊑_ CP
          (Flow GC a · Flow GC b)
          (Flow GC (a · b))

open QuanticNucleus public
-- Stable points are closed under join, and under “reflected” multiplication.

module QuanticNucleusLocal {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  {JP : JoinPrequantale CP}
  (N : QuanticNucleus JP)
  where
  open JoinPrequantale JP
  open FinSup FS
  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R
  private
    GC₀ : GuardedClosure CP
    GC₀ = GC N

  stable-⊔ᶠ
    : Stable {CP = CP} (Flow GC₀)
    → Stable {CP = CP} (Flow GC₀)
    → Stable {CP = CP} (Flow GC₀)
  stable-⊔ᶠ x y =
    mkStable
      (elem x ⊔ᶠ elem y)
      Flow⊔≤⊔
    where
      Flow⊔≤⊔
        : _⊑_ CP (Flow GC₀ (elem x ⊔ᶠ elem y)) (elem x ⊔ᶠ elem y)
      Flow⊔≤⊔ =
        begin⊑
          Flow GC₀ (elem x ⊔ᶠ elem y) ⊑⟨ fst (preserves-⊔ᶠ≈ N (elem x) (elem y)) ⟩
          (Flow GC₀ (elem x) ⊔ᶠ Flow GC₀ (elem y))
            ⊑⟨ LogOS.LT.Sup.FinSup.FinSupLocal.⊔ᶠ-mono FS (stable x) (stable y) ⟩
          (elem x ⊔ᶠ elem y) ∎⊑

  stable-·
    : Stable {CP = CP} (Flow GC₀)
    → Stable {CP = CP} (Flow GC₀)
    → Stable {CP = CP} (Flow GC₀)
  stable-· x y =
    mkStable
      (Flow GC₀ (elem x · elem y))
      (GuardedClosure.idemp-lax GC₀ (elem x · elem y))

  stable-over-approx-least
    : ∀ {a}
    → (z : Stable {CP = CP} (Flow GC₀))
    → _⊑_ CP a (elem z)
    → _⊑_ CP (Flow GC₀ a) (elem z)
  stable-over-approx-least {a = a} z a≤z =
    begin⊑
      Flow GC₀ a ⊑⟨ GuardedClosure.mono GC₀ a≤z ⟩
      Flow GC₀ (elem z) ⊑⟨ stable z ⟩
      elem z ∎⊑

  stable-·-least
    : ∀ (x y z : Stable {CP = CP} (Flow GC₀))
    → _⊑_ CP (elem x · elem y) (elem z)
    → _⊑_ CP (elem (stable-· x y)) (elem z)
  stable-·-least x y z xy≤z =
    stable-over-approx-least z xy≤z

  stableJoinList
    : Stable {CP = CP} (Flow GC₀)
    → List (Stable {CP = CP} (Flow GC₀))
    → Stable {CP = CP} (Flow GC₀)
  stableJoinList x [] = x
  stableJoinList x (y ∷ ys) =
    stableJoinList (stable-⊔ᶠ x y) ys

  stableJoinList-least
    : ∀ (x : Stable {CP = CP} (Flow GC₀))
        (xs : List (Stable {CP = CP} (Flow GC₀)))
        (z : Stable {CP = CP} (Flow GC₀))
    → _⊑_ CP (elem x) (elem z)
    → (∀ {y} → y ∈ xs → _⊑_ CP (elem y) (elem z))
    → _⊑_ CP (elem (stableJoinList x xs)) (elem z)
  stableJoinList-least x [] z x≤z _ =
    x≤z
  stableJoinList-least x (y ∷ ys) z x≤z ys≤z =
    stableJoinList-least
      (stable-⊔ᶠ x y)
      ys
      z
      (⊔ᶠ-least x≤z (ys≤z here))
      (λ {w} w∈ys → ys≤z (there w∈ys))

  record LeastStableMultiplicativeApproximation
    : Set (lsuc (ℓCon ⊔ ℓRel))
    where
    field
      theorem-stableJoinList
        : Stable {CP = CP} (Flow GC₀)
        → List (Stable {CP = CP} (Flow GC₀))
        → Stable {CP = CP} (Flow GC₀)

      theorem-stableJoinList-least
        : ∀ (x : Stable {CP = CP} (Flow GC₀))
            (xs : List (Stable {CP = CP} (Flow GC₀)))
            (z : Stable {CP = CP} (Flow GC₀))
        → _⊑_ CP (elem x) (elem z)
        → (∀ {y} → y ∈ xs → _⊑_ CP (elem y) (elem z))
        → _⊑_ CP (elem (theorem-stableJoinList x xs)) (elem z)

      theorem-stable-·-least
        : ∀ (x y z : Stable {CP = CP} (Flow GC₀))
        → _⊑_ CP (elem x · elem y) (elem z)
        → _⊑_ CP (elem (stable-· x y)) (elem z)

  leastStableMultiplicativeApproximation : LeastStableMultiplicativeApproximation
  leastStableMultiplicativeApproximation =
    record
      { theorem-stableJoinList = stableJoinList
      ; theorem-stableJoinList-least = stableJoinList-least
      ; theorem-stable-·-least = stable-·-least
      }
