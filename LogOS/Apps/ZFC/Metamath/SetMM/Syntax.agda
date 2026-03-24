{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Syntax where

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  )

open import LogOS.Apps.ZFC.Proof.Syntax as ZF using
  ( Term; Formula
  ; ⊥F; _∈F_; _≈F_
  ; _⇒_; _∧F_; _∨F_; _↔F_
  ; ∀F; ∃F
  )

-- Parametric FO syntax: ZFC FO constructors + Metamath-style wff metavariables.
data PFormula : Set where
  metaF : ℕ → PFormula
  botF  : PFormula
  notPF : PFormula → PFormula
  _∈PF_ : Term → Term → PFormula
  _≈PF_ : Term → Term → PFormula
  _⇒PF_ : PFormula → PFormula → PFormula
  _∧PF_ : PFormula → PFormula → PFormula
  _∨PF_ : PFormula → PFormula → PFormula
  _↔PF_ : PFormula → PFormula → PFormula
  ∀PF   : (xTok : ℕ) → PFormula → PFormula
  ∃PF   : (xTok : ℕ) → PFormula → PFormula

infixl 35 _∈PF_ _≈PF_
infixr 30 _⇒PF_
infixr 25 _∧PF_
infixr 24 _∨PF_
infixr 23 _↔PF_

-- Drop metas (fails if a metavariable occurs).
mutual
  toFormula : PFormula → Maybe Formula
  toFormula (metaF _) = nothing
  toFormula botF = just ⊥F
  toFormula (notPF φ) with toFormula φ
  ... | just φ' = just (φ' ⇒ ⊥F)
  ... | nothing = nothing
  toFormula (t ∈PF u) = just (t ∈F u)
  toFormula (t ≈PF u) = just (t ≈F u)
  toFormula (φ ⇒PF ψ) = toFormula₂ (λ p q → p ⇒ q) φ ψ
  toFormula (φ ∧PF ψ) = toFormula₂ (λ p q → p ∧F q) φ ψ
  toFormula (φ ∨PF ψ) = toFormula₂ (λ p q → p ∨F q) φ ψ
  toFormula (φ ↔PF ψ) = toFormula₂ (λ p q → p ↔F q) φ ψ
  toFormula (∀PF _ φ) with toFormula φ
  ... | just φ' = just (∀F φ')
  ... | nothing = nothing
  toFormula (∃PF _ φ) with toFormula φ
  ... | just φ' = just (∃F φ')
  ... | nothing = nothing

  toFormula₂ : (Formula → Formula → Formula) → PFormula → PFormula → Maybe Formula
  toFormula₂ mk p q with toFormula p
  ... | nothing = nothing
  ... | just φ' with toFormula q
  ... | just ψ' = just (mk φ' ψ')
  ... | nothing = nothing
