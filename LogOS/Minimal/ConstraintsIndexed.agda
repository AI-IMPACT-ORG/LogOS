{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.ConstraintsIndexed where

-- ============================================================================
-- SHARED CORE: FREE CONSTRAINT ALGEBRA WITH OPTIONAL ATOMS (INDEXED)
--
-- This module factors the common construction behind:
-- - `LogOS.Minimal.Constraints`           (no atoms; recovered by taking Atom = ⊥)
-- - `LogOS.Minimal.ConstraintsOverSig`    (atoms indexed by interface objects)
--
-- The design is “indexed” to allow both:
-- - a trivial one-point index (for the classic free constraint algebra), and
-- - index-by-signature (for a functorial sentence/program layer).
-- ============================================================================

open import LogOS.Prelude
open import LogOS.Prelude using (_×_; _,_)

open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.ConAlg

module With
  {ι ℓ : Level}
  (Idx  : Set ι)
  (Atom : Idx → Set ℓ)
  where

  infixl 7 _⊗∂_ _⊗b_
  infix 4 _≤∂_ _≤b_

  mutual
    data Con∂ (i : Idx) : Set ℓ where
      I∂    : Con∂ i
      _⊗∂_  : Con∂ i → Con∂ i → Con∂ i
      bnd   : Conb i → Con∂ i
      atom∂ : Atom i → Con∂ i

    data Conb (i : Idx) : Set ℓ where
      Ib    : Conb i
      _⊗b_  : Conb i → Conb i → Conb i
      ext   : Con∂ i → Conb i

  -- Atoms are boundary-only in the core syntax.
  -- A bulk “atom” can be represented canonically via the adjunction boundary map.

  atomᵇ : ∀ {i : Idx} → Atom i → Conb i
  atomᵇ a = ext (atom∂ a)

  mutual
    data _≤∂_ {i : Idx} : Con∂ i → Con∂ i → Set ℓ where
      refl∂    : ∀ {x} → x ≤∂ x
      trans∂   : ∀ {x y z} → x ≤∂ y → y ≤∂ z → x ≤∂ z
      cong⊗∂   : ∀ {x x' y y'} → x ≤∂ x' → y ≤∂ y' → (x ⊗∂ y) ≤∂ (x' ⊗∂ y')
      unitbnd  : ∀ {c} → c ≤∂ bnd (ext c)
      bnd-⊗    : ∀ {x y} → bnd (x ⊗b y) ≤∂ (bnd x ⊗∂ bnd y)
      bnd-I    : bnd Ib ≤∂ I∂

    data _≤b_ {i : Idx} : Conb i → Conb i → Set ℓ where
      reflb    : ∀ {x} → x ≤b x
      transb   : ∀ {x y z} → x ≤b y → y ≤b z → x ≤b z
      cong⊗b   : ∀ {x x' y y'} → x ≤b x' → y ≤b y' → (x ⊗b y) ≤b (x' ⊗b y')
      counit   : ∀ {d} → ext (bnd d) ≤b d
      ext-⊗    : ∀ {x y} → ext (x ⊗∂ y) ≤b (ext x ⊗b ext y)
      ext-I    : ext I∂ ≤b Ib

  conPreorder∂ : (i : Idx) → ConPreorder ℓ
  conPreorder∂ i = record { Con = Con∂ i ; _⊑_ = _≤∂_ ; refl = refl∂ ; trans = trans∂ }

  conPreorderb : (i : Idx) → ConPreorder ℓ
  conPreorderb i = record { Con = Conb i ; _⊑_ = _≤b_ ; refl = reflb ; trans = transb }

  BBfree : (i : Idx) → BulkBoundary ℓ
  BBfree i = record { bulk = conPreorderb i ; bnd = conPreorder∂ i }

  MBulkfree : (i : Idx) → MonoidalOps (BulkBoundary.bulk (BBfree i))
  MBulkfree i = record
    { _⊗_ = _⊗b_
    ; I   = Ib
    ; mono⊗ = λ {x} {x'} {y} {y'} px py → cong⊗b px py
    }

  MBndfree : (i : Idx) → MonoidalOps (BulkBoundary.bnd (BBfree i))
  MBndfree i = record
    { _⊗_ = _⊗∂_
    ; I   = I∂
    ; mono⊗ = λ {x} {x'} {y} {y'} px py → cong⊗∂ px py
    }

  Holofree : (i : Idx) → LaxMonoidalAdjunction (BBfree i) (MBulkfree i) (MBndfree i)
  Holofree i = record
    { core = record
        { ext = ext
        ; bnd = bnd
        ; unit-lax   = λ _ → unitbnd
        ; counit-lax = λ _ → counit
        }
    ; ext-⊗-lax = λ _ _ → ext-⊗
    ; ext-I-lax  = ext-I
    ; bnd-⊗-lax  = λ _ _ → bnd-⊗
    ; bnd-I-lax  = bnd-I
    }

  FreeConAlg : (i : Idx) → ConAlg {ℓ}
  FreeConAlg i =
    record { BB = BBfree i ; MBulk = MBulkfree i ; MBnd = MBndfree i ; Holo = Holofree i }

  -- Interpretation into any constraint algebra, given a valuation for atoms.

  mutual
    interp∂ : (i : Idx) {ℓA : Level} (A : ConAlg {ℓA}) (val : Atom i → ConAlg.Con_bnd A)
           → Con∂ i → ConAlg.Con_bnd A
    interp∂ i A val I∂ = ConAlg.I∂ A
    interp∂ i A val (x ⊗∂ y) = ConAlg._⊗∂_ A (interp∂ i A val x) (interp∂ i A val y)
    interp∂ i A val (bnd d) = LaxMonoidalAdjunction.bnd (ConAlg.Holo A) (interpb i A val d)
    interp∂ i A val (atom∂ a) = val a

    interpb : (i : Idx) {ℓA : Level} (A : ConAlg {ℓA}) (val : Atom i → ConAlg.Con_bnd A)
           → Conb i → ConAlg.Con_bulk A
    interpb i A val Ib = ConAlg.Ib A
    interpb i A val (x ⊗b y) = ConAlg._⊗b_ A (interpb i A val x) (interpb i A val y)
    interpb i A val (ext c) = ConAlg.ext A (interp∂ i A val c)

  interpb-atomᵇ
    : ∀ {i : Idx} {ℓA : Level}
      (A : ConAlg {ℓA}) (val : Atom i → ConAlg.Con_bnd A)
      (a : Atom i)
    → interpb i A val (atomᵇ a) ≡ ConAlg.ext A (val a)
  interpb-atomᵇ A val a = refl

  mutual
    interp∂-mono
      : (i : Idx) {ℓA : Level} (A : ConAlg {ℓA}) (val : Atom i → ConAlg.Con_bnd A)
        {x y : Con∂ i}
      → x ≤∂ y
      → ConAlg._⊑bnd_ A (interp∂ i A val x) (interp∂ i A val y)
    interp∂-mono i A val refl∂ = ConPreorder.refl (BulkBoundary.bnd (ConAlg.BB A))
    interp∂-mono i A val (trans∂ p q) =
      ConPreorder.trans (BulkBoundary.bnd (ConAlg.BB A))
        (interp∂-mono i A val p) (interp∂-mono i A val q)
    interp∂-mono i A val (cong⊗∂ px py) =
      let open MonoidalOps (ConAlg.MBnd A) in
      mono⊗ (interp∂-mono i A val px) (interp∂-mono i A val py)
    interp∂-mono i A val (unitbnd {c = c}) =
      ConAlg.unit-lax A (interp∂ i A val c)
    interp∂-mono i A val (bnd-⊗ {x = x} {y = y}) =
      ConAlg.bnd-⊗-lax A (interpb i A val x) (interpb i A val y)
    interp∂-mono i A val bnd-I =
      ConAlg.bnd-I-lax A

    interpb-mono
      : (i : Idx) {ℓA : Level} (A : ConAlg {ℓA}) (val : Atom i → ConAlg.Con_bnd A)
        {x y : Conb i}
      → x ≤b y
      → ConAlg._⊑bulk_ A (interpb i A val x) (interpb i A val y)
    interpb-mono i A val reflb = ConPreorder.refl (BulkBoundary.bulk (ConAlg.BB A))
    interpb-mono i A val (transb p q) =
      ConPreorder.trans (BulkBoundary.bulk (ConAlg.BB A))
        (interpb-mono i A val p) (interpb-mono i A val q)
    interpb-mono i A val (cong⊗b px py) =
      let open MonoidalOps (ConAlg.MBulk A) in
      mono⊗ (interpb-mono i A val px) (interpb-mono i A val py)
    interpb-mono i A val (counit {d = d}) =
      ConAlg.counit-lax A (interpb i A val d)
    interpb-mono i A val (ext-⊗ {x = x} {y = y}) =
      ConAlg.ext-⊗-lax A (interp∂ i A val x) (interp∂ i A val y)
    interpb-mono i A val ext-I =
      ConAlg.ext-I-lax A
