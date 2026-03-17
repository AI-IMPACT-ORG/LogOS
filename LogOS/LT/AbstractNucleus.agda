{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.AbstractNucleus where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Optional “locale-style nucleus” interface for boundaries.
--
-- The LT kernel only assumes a guarded closure (`GuardedClosure` / `Flow`):
-- monotone + inflationary + lax-idempotent.
--
-- In locale theory, a nucleus is usually a (strictly idempotent) closure operator
-- on opens that additionally preserves finite meets (and hence ⊤).
--
-- In the preorder-first LogOS setting, the natural minimal upgrade is:
-- - supply finite meets on the boundary (as finite joins on `Opp`), and
-- - require `Flow` to preserve those meets up to mutual refinement (`≈`).
--
-- This keeps the core kernel weak, but supports the “nucleus/sublocale” reading
-- *literally* once such boundary algebra is supplied.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; Opp)
open import LogOS.LT.Flow using (GuardedClosure; Stable; Flow; mkStable; elem; stable)
open import LogOS.LT.Sup.FinSup using (FinSup)

-- Finite meets/top on `CP` are finite joins/bottom on `Opp CP`.
FinMeet
  : ∀ {ℓCon ℓRel : Level}
  → ConPreorder ℓCon ℓRel
  → Set (lsuc (ℓCon ⊔ ℓRel))
FinMeet CP = FinSup (Opp CP)

infixl 7 _⊓ᶠ_

_⊓ᶠ_
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → FinMeet CP
  → Con CP → Con CP → Con CP
_⊓ᶠ_ {CP = CP} FM a b = FinSup._⊔ᶠ_ FM a b

⊤ᶠ
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → FinMeet CP
  → Con CP
⊤ᶠ {CP = CP} FM = FinSup.⊥ᶠ FM

-- A locale-style nucleus: `Flow` preserves finite meets/top (up to `≈`).
record Nucleus {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    GC : GuardedClosure CP
    meet : FinMeet CP

    preserves-⊤ : _≈_ CP (Flow GC (⊤ᶠ meet)) (⊤ᶠ meet)
    preserves-⊓
      : ∀ a b
      → _≈_ CP
          (Flow GC (_⊓ᶠ_ meet a b))
          (_⊓ᶠ_ meet (Flow GC a) (Flow GC b))

open Nucleus public
-- Derived: stable points are closed under finite meets, when `Flow` preserves meets.
stable-⊓
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (N : Nucleus CP)
  → Stable {CP = CP} (Flow (GC N))
  → Stable {CP = CP} (Flow (GC N))
  → Stable {CP = CP} (Flow (GC N))
stable-⊓ {CP = CP} N x y =
  mkStable
    (_⊓ᶠ_ (meet N) (elem x) (elem y))
    Flowxy≤xy
  where
    module R = LogOS.Prelude.RefinementKit.Reasoning CP
    open R
    GC₀ = GC N
    FM = meet N

    -- Meet projections, derived from join upper bounds in `Opp CP`.
    --
    -- `⊔ᶠ-ub₁` in `Opp` is: a ⊑Opp (a ⊔ b), i.e. (a ⊔ b) ⊑ a in `CP`.
    ⊓ᶠ-lb₁
      : ∀ a b
      → _⊑_ CP (_⊓ᶠ_ FM a b) a
    ⊓ᶠ-lb₁ a b = FinSup.⊔ᶠ-ub₁ {CP = Opp CP} FM a b

    ⊓ᶠ-lb₂
      : ∀ a b
      → _⊑_ CP (_⊓ᶠ_ FM a b) b
    ⊓ᶠ-lb₂ a b = FinSup.⊔ᶠ-ub₂ {CP = Opp CP} FM a b

    Flowxy≤Flowx⊓Flowy
      : _⊑_ CP
          (Flow GC₀ (_⊓ᶠ_ FM (elem x) (elem y)))
          (_⊓ᶠ_ FM (Flow GC₀ (elem x)) (Flow GC₀ (elem y)))
    Flowxy≤Flowx⊓Flowy = fst (preserves-⊓ N (elem x) (elem y))

    Flowx⊓Flowy≤x⊓y
      : _⊑_ CP
          (_⊓ᶠ_ FM (Flow GC₀ (elem x)) (Flow GC₀ (elem y)))
          (_⊓ᶠ_ FM (elem x) (elem y))
    Flowx⊓Flowy≤x⊓y =
      -- Use “meet leastness” (join leastness in `Opp`):
      -- show `Flowx ⊓ Flowy` is a lower bound of `x` and `y`.
      FinSup.⊔ᶠ-least {CP = Opp CP} FM
        (begin⊑
          (_⊓ᶠ_ FM (Flow GC₀ (elem x)) (Flow GC₀ (elem y)))
            ⊑⟨ ⊓ᶠ-lb₁ (Flow GC₀ (elem x)) (Flow GC₀ (elem y)) ⟩
          Flow GC₀ (elem x) ⊑⟨ stable x ⟩
          elem x ∎⊑)
        (begin⊑
          (_⊓ᶠ_ FM (Flow GC₀ (elem x)) (Flow GC₀ (elem y)))
            ⊑⟨ ⊓ᶠ-lb₂ (Flow GC₀ (elem x)) (Flow GC₀ (elem y)) ⟩
          Flow GC₀ (elem y) ⊑⟨ stable y ⟩
          elem y ∎⊑)

    Flowxy≤xy
      : _⊑_ CP
          (Flow GC₀ (_⊓ᶠ_ FM (elem x) (elem y)))
          (_⊓ᶠ_ FM (elem x) (elem y))
    Flowxy≤xy =
      begin⊑
        Flow GC₀ (_⊓ᶠ_ FM (elem x) (elem y)) ⊑⟨ Flowxy≤Flowx⊓Flowy ⟩
        (_⊓ᶠ_ FM (Flow GC₀ (elem x)) (Flow GC₀ (elem y)))
          ⊑⟨ Flowx⊓Flowy≤x⊓y ⟩
        (_⊓ᶠ_ FM (elem x) (elem y)) ∎⊑
