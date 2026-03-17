{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder.Indexed where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Indexed refinement preorders (family of preorders sharing one carrier).
--
-- This is the "context-indexed" analogue of `ConPreorder`:
-- - `_⊑_ i x y` is refinement at index `i`,
-- - equivalence `_≈_` is derived as mutual refinement at each index.
--
-- Naming note (presentation only):
-- this generic module uses the neutral binder name `Index`;
-- context-facing approximation surfaces may rename it to `Context` when the
-- intended reading is “approximation regime” (budget/time/scale/observables).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)

record IndexedConPreorder
  {ℓI ℓA : Level}
  (Index : Set ℓI)
  (A : Set ℓA)
  (ℓRel : Level)
  : Set (lsuc (ℓI ⊔ ℓA ⊔ ℓRel)) where
  infix 4 _⊑_ _≈_
  field
    _⊑_ : Index → A → A → Set ℓRel
    reflAt : ∀ {i x} → _⊑_ i x x
    transAt : ∀ {i x y z} → _⊑_ i x y → _⊑_ i y z → _⊑_ i x z

  -- Derived equivalence (mutual refinement).
  _≈_ : Index → A → A → Set ℓRel
  _≈_ i x y = (_⊑_ i x y) × (_⊑_ i y x)

  ≈-reflAt : ∀ {i x} → _≈_ i x x
  ≈-reflAt {i} {x} = (reflAt {i = i} {x = x} , reflAt {i = i} {x = x})

  ≈-symAt : ∀ {i x y} → _≈_ i x y → _≈_ i y x
  ≈-symAt (xy , yx) = (yx , xy)

  ≈-transAt : ∀ {i x y z} → _≈_ i x y → _≈_ i y z → _≈_ i x z
  ≈-transAt {i = i} (xy , yx) (yz , zy) =
    ( transAt {i = i} xy yz
    , transAt {i = i} zy yx
    )

  -- “Sandwich” refinement through a shared middle point (at a fixed index).
  --
  -- If two constraints are observationally equivalent to the same middle constraint
  -- at index `i`, then they refine each other at `i`; in particular we can project
  -- one refinement direction by transitivity.
  sandwichAt : ∀ {i x y m} → _≈_ i x m → _≈_ i y m → _⊑_ i x y
  sandwichAt {i = i} (x≤m , _) (_ , m≤y) =
    transAt {i = i} x≤m m≤y

open IndexedConPreorder public
mkIndexedConPreorder
  : ∀ {ℓI ℓA ℓRel}
    {Index : Set ℓI}
    {A : Set ℓA}
  → (_⊑_ : Index → A → A → Set ℓRel)
  → (reflAt : ∀ {i x} → _⊑_ i x x)
  → (transAt : ∀ {i x y z} → _⊑_ i x y → _⊑_ i y z → _⊑_ i x z)
  → IndexedConPreorder Index A ℓRel
mkIndexedConPreorder _⊑_ reflAt transAt =
  record
    { _⊑_ = _⊑_
    ; reflAt = λ {i} {x} → reflAt {i = i} {x = x}
    ; transAt =
        λ {i} {x} {y} {z} xy yz →
          transAt {i = i} {x = x} {y = y} {z = z} xy yz
    }

-- Fix an index to obtain an ordinary refinement preorder.
atCP
  : ∀ {ℓI ℓA ℓRel}
    {Index : Set ℓI}
    {A : Set ℓA}
  → IndexedConPreorder Index A ℓRel
  → Index
  → ConPreorder ℓA ℓRel
atCP {A = A} ICP i =
  record
    { Con = A
    ; _⊑_ = IndexedConPreorder._⊑_ ICP i
    ; refl = λ {c} → IndexedConPreorder.reflAt ICP {i = i} {x = c}
    ; trans =
        λ {a} {b} {c} ab bc →
          IndexedConPreorder.transAt ICP {i = i} {x = a} {y = b} {z = c} ab bc
    }
