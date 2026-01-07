{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.QNatTop where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ; weakenRight)
open import Data.NatExtra using (_⊔ℕ_; max-left; max-right; ⊔ℕ-least; +-assoc; +-zeroˡ; +-zeroʳ; ⊔ℕ-distrib-+ʳ; ⊔ℕ-distrib-+ˡ)
open import Data.Ordinal as Ord using (Ord; fin; ω)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps)

-- Nat-valued grades with an explicit top element ω.
--
-- This avoids the “everything ≤ everything” trivial order: grades are ordered
-- by the usual ≤ on naturals, extended with ω as a top.

infix 4 _≤o_
_≤o_ : Ord → Ord → Set
fin m ≤o fin n = m ≤ℕ n
fin _ ≤o ω     = ⊤
ω     ≤o fin _ = ⊥
ω     ≤o ω     = ⊤

≤o-refl : ∀ {g} → g ≤o g
≤o-refl {fin _} = ≤ℕ-refl
≤o-refl {ω} = tt

≤o-trans : ∀ {a b c} → a ≤o b → b ≤o c → a ≤o c
≤o-trans {fin _} {fin _} {fin _} ab bc = trans≤ℕ ab bc
≤o-trans {fin _} {fin _} {ω} _ _ = tt
≤o-trans {fin _} {ω} {ω} _ _ = tt
≤o-trans {fin _} {ω}     {fin _} _  ()
≤o-trans {ω}     {fin _} {_}     () _
≤o-trans {ω}     {ω}     {fin _} _  ()
≤o-trans {ω}     {ω}     {ω}     _  _  = tt

infixl 6 _⊔o_
_⊔o_ : Ord → Ord → Ord
fin m ⊔o fin n = fin (m ⊔ℕ n)
ω     ⊔o _     = ω
fin _ ⊔o ω     = ω

⊥o : Ord
⊥o = fin zero

⊥o-least : ∀ g → ⊥o ≤o g
⊥o-least (fin _) = z≤n
⊥o-least ω = tt

⊔o-ub₁ : ∀ a b → a ≤o (a ⊔o b)
⊔o-ub₁ (fin m) (fin n) = max-left m n
⊔o-ub₁ ω _ = tt
⊔o-ub₁ (fin _) ω = tt

⊔o-ub₂ : ∀ a b → b ≤o (a ⊔o b)
⊔o-ub₂ (fin m) (fin n) = max-right m n
⊔o-ub₂ ω (fin _) = tt
⊔o-ub₂ ω ω = tt
⊔o-ub₂ (fin _) ω = tt

⊔o-least : ∀ {a b c} → a ≤o c → b ≤o c → (a ⊔o b) ≤o c
⊔o-least {a = fin _} {b = fin _} {c = ω} _ _ = tt
⊔o-least {a = fin _} {b = ω} {c = ω} _ _ = tt
⊔o-least {a = ω} {b = fin _} {c = ω} _ _ = tt
⊔o-least {a = ω} {b = ω} {c = ω} _ _ = tt
⊔o-least {a = fin _} {b = fin _} {c = fin _} a≤c b≤c = ⊔ℕ-least a≤c b≤c
⊔o-least {a = ω} {c = fin _} () _
⊔o-least {b = ω} {c = fin _} _ ()

infixl 7 _+o_
_+o_ : Ord → Ord → Ord
fin m +o fin n = fin (m + n)
fin _ +o ω     = ω
ω     +o _     = ω

+o-assoc : ∀ a b c → (a +o b) +o c ≡ a +o (b +o c)
+o-assoc (fin a) (fin b) (fin c) = cong fin (+-assoc a b c)
+o-assoc (fin _) (fin _) ω = refl
+o-assoc (fin _) ω _ = refl
+o-assoc ω _ _ = refl

+o-idl : ∀ a → (fin zero +o a) ≡ a
+o-idl (fin a) = cong fin (+-zeroˡ a)
+o-idl ω = refl

+o-idr : ∀ a → (a +o fin zero) ≡ a
+o-idr (fin a) = cong fin (+-zeroʳ a)
+o-idr ω = refl

+o-distl-⊔ : ∀ a b c → ((a ⊔o b) +o c) ≡ ((a +o c) ⊔o (b +o c))
+o-distl-⊔ (fin a) (fin b) (fin c) = cong fin (⊔ℕ-distrib-+ʳ a b c)
+o-distl-⊔ (fin _) (fin _) ω = refl
+o-distl-⊔ (fin _) ω (fin _) = refl
+o-distl-⊔ (fin _) ω ω = refl
+o-distl-⊔ ω _ _ = refl

+o-distr-⊔ : ∀ a b c → (a +o (b ⊔o c)) ≡ ((a +o b) ⊔o (a +o c))
+o-distr-⊔ (fin a) (fin b) (fin c) = cong fin (⊔ℕ-distrib-+ˡ a b c)
+o-distr-⊔ (fin _) (fin _) ω = refl
+o-distr-⊔ (fin _) ω (fin _) = refl
+o-distr-⊔ (fin _) ω ω = refl
+o-distr-⊔ ω _ _ = refl

-- Adapter -------------------------------------------------------------------

QNatTop : QAdapter lzero
QNatTop = record
  { Scale = Ord
  ; _≤s_ = _≤o_
  ; ≤s-refl = ≤o-refl
  ; ≤s-trans = ≤o-trans
  ; _⊔s_ = _⊔o_
  ; ⊥s = ⊥o
  ; ⊥s-least = ⊥o-least
  ; ⊔s-ub₁ = ⊔o-ub₁
  ; ⊔s-ub₂ = ⊔o-ub₂
  ; ⊔s-least = ⊔o-least
  ; _·_ = _+o_
  ; e = fin zero
  ; ·-assoc = +o-assoc
  ; ·-idl = +o-idl
  ; ·-idr = +o-idr
  ; ·-mono = +o-mono
  ; ·-distl-⊔s = +o-distl-⊔
  ; ·-distr-⊔s = +o-distr-⊔
  ; _≤p_ = _≤o_
  ; ≤p-refl = ≤o-refl
  ; ≤p-trans = ≤o-trans
  ; Time = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; τ = fin
  ; +-assoc = +-assoc
  ; +-idl = +-zeroˡ
  ; +-idr = +-zeroʳ
  ; τ-+ = λ _ _ → refl
  ; τ-zero = refl
  }
  where
    leAddLeft : ∀ b c → c ≤ℕ (b + c)
    leAddLeft zero    c = ≤ℕ-refl
    leAddLeft (suc b) c = weakenRight (leAddLeft b c)

    monoPlusRight : ∀ {a b c} → a ≤ℕ b → (a + c) ≤ℕ (b + c)
    monoPlusRight {b = b} {c = c} z≤n = leAddLeft b c
    monoPlusRight (s≤s p) = s≤s (monoPlusRight p)

    monoPlusLeft : ∀ {a b} → a ≤ℕ b → ∀ c → (c + a) ≤ℕ (c + b)
    monoPlusLeft p zero    = p
    monoPlusLeft p (suc c) = s≤s (monoPlusLeft p c)

    +-mono : ∀ {a a' b b'} → a ≤ℕ a' → b ≤ℕ b' → (a + b) ≤ℕ (a' + b')
    +-mono {a' = a'} a≤a' b≤b' =
      trans≤ℕ (monoPlusRight a≤a') (monoPlusLeft b≤b' a')

    leω : ∀ x → x ≤o ω
    leω (fin _) = tt
    leω ω = tt

    +o-mono : ∀ {a b c d} → a ≤o b → c ≤o d → (a +o c) ≤o (b +o d)
    +o-mono {a = a} {b = ω} {c = c} _ _ = leω (a +o c)
    +o-mono {a = a} {b = fin _} {c = c} {d = ω} _ _ = leω (a +o c)
    +o-mono {a = fin m} {b = fin n} {c = fin p} {d = fin q} ab cd =
      +-mono ab cd

-- Operational view: interpret finite grades as step budgets; ω as “unbounded”.
-- The `steps` projection remains total by choosing a conventional finite readout.

budgetOrd : Ord → ℕ
budgetOrd (fin n) = n
budgetOrd ω = zero

stepsOrd : ℕ → ℕ
stepsOrd n = n

scaleOps : ScaleOps QNatTop
scaleOps = record { budget = budgetOrd ; steps = stepsOrd }
