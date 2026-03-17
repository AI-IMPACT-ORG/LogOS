{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Sup.FinSup where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Finite suprema and extremal points on boundaries.
--
-- This is the “finite algebra” half of the optional completeness layer:
-- `FinSup` gives bottom + binary join (specified by universal properties).
--
-- It also defines minimal pointed structure (`HasBottom`, `HasTop`) and
-- fixed-point vocabulary used by the μ/ν-calculus spines.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder; Con; _⊑_; _≈_; refl⊑; MonoOn; Opp )

-- --------------------------------------------------------------------------
-- Finite suprema (binary join + bottom).

record FinSup {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel) : Set (lsuc (ℓCon ⊔ ℓRel)) where
  infixl 6 _⊔ᶠ_
  field
    _⊔ᶠ_ : Con CP → Con CP → Con CP
    ⊥ᶠ   : Con CP

    ⊥ᶠ-least : ∀ a → _⊑_ CP ⊥ᶠ a

    ⊔ᶠ-ub₁   : ∀ a b → _⊑_ CP a (a ⊔ᶠ b)
    ⊔ᶠ-ub₂   : ∀ a b → _⊑_ CP b (a ⊔ᶠ b)

    ⊔ᶠ-least : ∀ {a b c} → _⊑_ CP a c → _⊑_ CP b c → _⊑_ CP (a ⊔ᶠ b) c

-- Minimal pointed structure (needed for fixed-point spines).
record HasBottom {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel) : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    ⊥ᵇ : Con CP
    ⊥ᵇ-least : ∀ a → _⊑_ CP ⊥ᵇ a

record HasTop {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel) : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    ⊤ᵇ : Con CP
    ⊤ᵇ-greatest : ∀ a → _⊑_ CP a ⊤ᵇ

-- Fixed-point vocabulary (μ-calculus semantics layer).
PrefixPoint
  : ∀ {ℓCon ℓRel : Level}
  → (CP : ConPreorder ℓCon ℓRel)
  → (Con CP → Con CP)
  → Con CP
  → Set ℓRel
PrefixPoint CP f x = _⊑_ CP (f x) x

PostfixPoint
  : ∀ {ℓCon ℓRel : Level}
  → (CP : ConPreorder ℓCon ℓRel)
  → (Con CP → Con CP)
  → Con CP
  → Set ℓRel
PostfixPoint CP f x = _⊑_ CP x (f x)

FixedPoint≈
  : ∀ {ℓCon ℓRel : Level}
  → (CP : ConPreorder ℓCon ℓRel)
  → (Con CP → Con CP)
  → Con CP
  → Set ℓRel
FixedPoint≈ CP f x = _≈_ CP (f x) x

hasBottomFromFinSup
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → FinSup CP
  → HasBottom CP
hasBottomFromFinSup FS =
  record
    { ⊥ᵇ = FinSup.⊥ᶠ FS
    ; ⊥ᵇ-least = FinSup.⊥ᶠ-least FS
    }

hasBottomOppFromHasTop
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → HasTop CP
  → HasBottom (Opp CP)
hasBottomOppFromHasTop HT =
  record
    { ⊥ᵇ = HasTop.⊤ᵇ HT
    ; ⊥ᵇ-least = HasTop.⊤ᵇ-greatest HT
    }

hasTopFromHasBottomOpp
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → HasBottom (Opp CP)
  → HasTop CP
hasTopFromHasBottomOpp HB =
  record
    { ⊤ᵇ = HasBottom.⊥ᵇ HB
    ; ⊤ᵇ-greatest = HasBottom.⊥ᵇ-least HB
    }

module FinSupLocal {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel} (FS : FinSup CP) where
  open FinSup FS
  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R
  ⊔ᶠ-mono
    : ∀ {a a' b b'}
    → _⊑_ CP a a' → _⊑_ CP b b'
    → _⊑_ CP (a ⊔ᶠ b) (a' ⊔ᶠ b')
  ⊔ᶠ-mono {a} {a'} {b} {b'} aa' bb' =
    ⊔ᶠ-least
      (begin⊑
        a ⊑⟨ aa' ⟩
        a' ⊑⟨ ⊔ᶠ-ub₁ a' b' ⟩
        (a' ⊔ᶠ b') ∎⊑)
      (begin⊑
        b ⊑⟨ bb' ⟩
        b' ⊑⟨ ⊔ᶠ-ub₂ a' b' ⟩
        (a' ⊔ᶠ b') ∎⊑)

  -- Standard semilattice laws hold up to `≈` (mutual refinement).

  ⊔ᶠ-idem≈ : ∀ a → _≈_ CP (a ⊔ᶠ a) a
  ⊔ᶠ-idem≈ a =
    ( ⊔ᶠ-least (refl⊑ CP) (refl⊑ CP)
    , ⊔ᶠ-ub₁ a a
    )

  ⊔ᶠ-comm≈ : ∀ a b → _≈_ CP (a ⊔ᶠ b) (b ⊔ᶠ a)
  ⊔ᶠ-comm≈ a b =
    ( ⊔ᶠ-least (⊔ᶠ-ub₂ b a) (⊔ᶠ-ub₁ b a)
    , ⊔ᶠ-least (⊔ᶠ-ub₂ a b) (⊔ᶠ-ub₁ a b)
    )

  ⊔ᶠ-assoc≈ : ∀ a b c → _≈_ CP ((a ⊔ᶠ b) ⊔ᶠ c) (a ⊔ᶠ (b ⊔ᶠ c))
  ⊔ᶠ-assoc≈ a b c =
    ( lhs≤rhs , rhs≤lhs )
    where
      lhs≤rhs : _⊑_ CP ((a ⊔ᶠ b) ⊔ᶠ c) (a ⊔ᶠ (b ⊔ᶠ c))
      lhs≤rhs =
        ⊔ᶠ-least
          ab≤rhs
          c≤rhs
        where
          ab≤rhs : _⊑_ CP (a ⊔ᶠ b) (a ⊔ᶠ (b ⊔ᶠ c))
          ab≤rhs =
            ⊔ᶠ-least
              (⊔ᶠ-ub₁ a (b ⊔ᶠ c))
              (begin⊑
                b ⊑⟨ ⊔ᶠ-ub₁ b c ⟩
                (b ⊔ᶠ c) ⊑⟨ ⊔ᶠ-ub₂ a (b ⊔ᶠ c) ⟩
                (a ⊔ᶠ (b ⊔ᶠ c)) ∎⊑)

          c≤rhs : _⊑_ CP c (a ⊔ᶠ (b ⊔ᶠ c))
          c≤rhs =
            begin⊑
              c ⊑⟨ ⊔ᶠ-ub₂ b c ⟩
              (b ⊔ᶠ c) ⊑⟨ ⊔ᶠ-ub₂ a (b ⊔ᶠ c) ⟩
              (a ⊔ᶠ (b ⊔ᶠ c)) ∎⊑

      rhs≤lhs : _⊑_ CP (a ⊔ᶠ (b ⊔ᶠ c)) ((a ⊔ᶠ b) ⊔ᶠ c)
      rhs≤lhs =
        ⊔ᶠ-least
          a≤lhs
          bc≤lhs
        where
          a≤lhs : _⊑_ CP a ((a ⊔ᶠ b) ⊔ᶠ c)
          a≤lhs =
            begin⊑
              a ⊑⟨ ⊔ᶠ-ub₁ a b ⟩
              (a ⊔ᶠ b) ⊑⟨ ⊔ᶠ-ub₁ (a ⊔ᶠ b) c ⟩
              ((a ⊔ᶠ b) ⊔ᶠ c) ∎⊑

          bc≤lhs : _⊑_ CP (b ⊔ᶠ c) ((a ⊔ᶠ b) ⊔ᶠ c)
          bc≤lhs =
            ⊔ᶠ-least
              (begin⊑
                b ⊑⟨ ⊔ᶠ-ub₂ a b ⟩
                (a ⊔ᶠ b) ⊑⟨ ⊔ᶠ-ub₁ (a ⊔ᶠ b) c ⟩
                ((a ⊔ᶠ b) ⊔ᶠ c) ∎⊑)
              (⊔ᶠ-ub₂ (a ⊔ᶠ b) c)

  ⊔ᶠ-idl-⊥ᶠ≈ : ∀ a → _≈_ CP (⊥ᶠ ⊔ᶠ a) a
  ⊔ᶠ-idl-⊥ᶠ≈ a =
    ( ⊔ᶠ-least (⊥ᶠ-least a) (refl⊑ CP)
    , ⊔ᶠ-ub₂ ⊥ᶠ a
    )

  ⊔ᶠ-idr-⊥ᶠ≈ : ∀ a → _≈_ CP (a ⊔ᶠ ⊥ᶠ) a
  ⊔ᶠ-idr-⊥ᶠ≈ a =
    ( ⊔ᶠ-least (refl⊑ CP) (⊥ᶠ-least a)
    , ⊔ᶠ-ub₁ a ⊥ᶠ
    )
