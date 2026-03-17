{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.QAdapter.Definitional where

-- Definitional/bookkeeping equalities for quantitative adapters.

open import LogOS.Prelude
open import LogOS.Ports.Valuation.QAdapter using (QAdapter; QAdapterCore; qAdapterCore)

record QAdapterEqLaws {ℓ : Level} (C : QAdapterCore ℓ) : Set (lsuc ℓ) where
  open QAdapterCore C
  field
    ·-assoc : ∀ a b c → ((a · b) · c) ≡ (a · (b · c))
    ·-idl   : ∀ a → (e · a) ≡ a
    ·-idr   : ∀ a → (a · e) ≡ a
    ·-distl-⊔s : ∀ a b c → ((a ⊔s b) · c) ≡ ((a · c) ⊔s (b · c))
    ·-distr-⊔s : ∀ a b c → (a · (b ⊔s c)) ≡ ((a · b) ⊔s (a · c))

qAdapterEqLaws : ∀ {ℓ} (Q : QAdapter ℓ) → QAdapterEqLaws (qAdapterCore Q)
qAdapterEqLaws Q =
  record
    { ·-assoc = QAdapter.·-assoc Q
    ; ·-idl = QAdapter.·-idl Q
    ; ·-idr = QAdapter.·-idr Q
    ; ·-distl-⊔s = QAdapter.·-distl-⊔s Q
    ; ·-distr-⊔s = QAdapter.·-distr-⊔s Q
    }

mkQAdapter
  : ∀ {ℓ}
  → (C : QAdapterCore ℓ)
  → QAdapterEqLaws C
  → QAdapter ℓ
mkQAdapter C L =
  record
    { core = C
    ; ·-assoc = QAdapterEqLaws.·-assoc L
    ; ·-idl = QAdapterEqLaws.·-idl L
    ; ·-idr = QAdapterEqLaws.·-idr L
    ; ·-distl-⊔s = QAdapterEqLaws.·-distl-⊔s L
    ; ·-distr-⊔s = QAdapterEqLaws.·-distr-⊔s L
    }
