{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Diagonal where

open import LogOS.Prelude
open import Data.Product using (Σ; _,_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Theorems.Code.Core as Code
-- (import kept minimal to avoid heavy commitments)

-- Conditional diagonalization assumption packaged as a record: models or meta-proofs can
-- supply this to use Tarski/Rice-style arguments without global postulates.

record Diagonal {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                (K : Kernel Sig Q)
                : Set (lsuc ℓ) where
  field
    diagonal
      : (F : Kernel.Code K → Kernel.Code K)
      → Σ (Kernel.Code K) (λ γ → Kernel.Body K (F γ) ≡ Kernel.Body K γ)

-- Helpers: transport a diagonal witness to boundary-level equalities.

Diagonal-Body∂-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (D   : Diagonal K)
    (F   : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ γ →
       Kernel.Body∂ K (Kernel.decode K (F γ)) ≡
       Kernel.Body∂ K (Kernel.decode K γ))
Diagonal-Body∂-eq K D F with Diagonal.diagonal D F
... | γ , eq =
  let step₁ = Kernel.body-decode K (F γ)
      step₂ = Kernel.body-decode K γ
      bodyEq = trans (sym step₁) (trans (cong (Kernel.decode K) eq) step₂)
  in γ , bodyEq

Diagonal-FlowEndo-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (D   : Diagonal K)
    (F   : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ γ →
       Endo.fn (Flow-Endo K)
         (Kernel.Body∂ K (Kernel.decode K (F γ)))
       ≡ Endo.fn (Flow-Endo K)
         (Kernel.Body∂ K (Kernel.decode K γ)))
Diagonal-FlowEndo-eq K D F with Diagonal.diagonal D F
... | γ , eq =
  let guardEq = cong (Kernel.Guard K) eq
      decEq = cong (Kernel.decode K) guardEq
      lhs   = Code.decode-FlowCode-eq K (F γ)
      rhs   = Code.decode-FlowCode-eq K γ
      flowEq = trans (sym lhs) (trans decEq rhs)
  in γ , flowEq
