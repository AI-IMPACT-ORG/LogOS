{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS.Bisimulation where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Theorems.Boundary.Reflection as BR

-- “Full bisimulation” in the most LogOS-native OS sense:
-- bisimulation is *boundary observational equivalence*.
--
-- This avoids inventing an internal small-step relation: LogOS is an open system,
-- so the only behaviour that matters is what the explicit boundary can observe.
--
-- If you additionally assume observational completeness (Extension),
-- you recover a full-abstraction statement: bisimilarity ⇔ decode-equality.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) where
  open Kernel K

  -- Bisimulation on codes (by definition, boundary observational equivalence).
  Bisim : Code → Code → Set ℓ
  Bisim = BR._≈∂_ K

  bisim-refl : ∀ γ → Bisim γ γ
  bisim-refl γ p = record { to = λ x → x ; from = λ x → x }

  bisim-sym : ∀ {γ δ} → Bisim γ δ → Bisim δ γ
  bisim-sym eq p = record { to = _↔_.from (eq p) ; from = _↔_.to (eq p) }

  bisim-trans : ∀ {γ δ ε} → Bisim γ δ → Bisim δ ε → Bisim γ ε
  bisim-trans gd de p =
    record
      { to   = λ s → _↔_.to (de p) (_↔_.to (gd p) s)
      ; from = λ s → _↔_.from (gd p) (_↔_.from (de p) s)
      }

  decode≡→bisim : ∀ {γ δ} → decode γ ≡ decode δ → Bisim γ δ
  decode≡→bisim = BR.decode≡→≈∂ K

  -- Kernel reflection respects bisimulation immediately (reify is observation-inert).
  reify-bisim : ∀ γ → Bisim (reify γ) γ
  reify-bisim = BR.reify≈∂ K
