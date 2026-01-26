{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Domain where

open import LogOS.Prelude

open import LogOS.Minimal.Con
open import LogOS.Prelude.NatOrder using (_≤ℕ_; total≤ℕ; z≤n; s≤s)
import LogOS.Minimal.Truth as Truth

-- Re-export domain-theoretic structure from the guarded core.
-- This module introduces no new axioms; it only names existing interfaces.

OmegaCPO : ∀ {ℓ} → ConPreorder ℓ → Set (lsuc ℓ)
OmegaCPO {ℓ} = Truth.GuardedCore.OmegaCPO {ℓ}

FiniteFirst
  : ∀ {ℓ} (CP : ConPreorder ℓ)
  → Truth.GuardedCore.GuardedClosure {ℓ} CP
  → OmegaCPO CP
  → Set (lsuc ℓ)
FiniteFirst {ℓ} CP = Truth.GuardedCore.FiniteFirst {ℓ} CP

-- Directedness and ω-chains (lightweight, interface only).

record Directed {ℓ ℓI}
                (CP : ConPreorder ℓ)
                (I : Set ℓI)
                (f : I → ConPreorder.Con CP)
                : Set (lsuc (ℓ ⊔ ℓI)) where
  open ConPreorder CP
  field
    upper : ∀ i j → Σ I (λ k → (_⊑_ (f i) (f k)) × (_⊑_ (f j) (f k)))

record ωChain {ℓ}
              (CP : ConPreorder ℓ)
              : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    seq  : ℕ → Con
    mono : ∀ n → _⊑_ (seq n) (seq (suc n))

ωChain-shift
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → ωChain CP → ωChain CP
ωChain-shift {CP = CP} ch =
  record
    { seq = λ n → ωChain.seq ch (suc n)
    ; mono = λ n → ωChain.mono ch (suc n)
    }

ωChain-from-zero
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (ch : ωChain CP)
  → (n : ℕ)
  → ConPreorder._⊑_ CP (ωChain.seq ch zero) (ωChain.seq ch n)
ωChain-from-zero {CP = CP} ch zero = ConPreorder.refl CP
ωChain-from-zero {CP = CP} ch (suc n) =
  ConPreorder.trans CP
    (ωChain-from-zero ch n)
    (ωChain.mono ch n)

ωChain-mono≤ℕ
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (ch : ωChain CP)
  → {m n : ℕ}
  → m ≤ℕ n
  → ConPreorder._⊑_ CP (ωChain.seq ch m) (ωChain.seq ch n)
ωChain-mono≤ℕ ch {n = n} z≤n =
  ωChain-from-zero ch n
ωChain-mono≤ℕ ch (s≤s mn) =
  ωChain-mono≤ℕ (ωChain-shift ch) mn

ωChain-directed
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (ch : ωChain CP)
  → Directed CP ℕ (ωChain.seq ch)
ωChain-directed {CP = CP} ch =
  -- Locale/domain intuition: ω-chains are directed systems.
  record
    { upper = λ i j → upper i j }
  where
    open ConPreorder CP
    upper : ∀ i j → Σ ℕ (λ k → (_⊑_ (ωChain.seq ch i) (ωChain.seq ch k))
                              × (_⊑_ (ωChain.seq ch j) (ωChain.seq ch k)))
    upper i j with total≤ℕ i j
    ... | inj₁ i≤j = (j , (ωChain-mono≤ℕ ch i≤j , ConPreorder.refl CP))
    ... | inj₂ j≤i = (i , (ConPreorder.refl CP , ωChain-mono≤ℕ ch j≤i))
