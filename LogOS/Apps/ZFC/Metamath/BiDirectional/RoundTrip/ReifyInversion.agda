{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip.ReifyInversion where

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  )

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Env using (fresh; termToToken)
open import LogOS.Apps.ZFC.Metamath.BiDirectional.Reify using (toPFormula; toPFormulaWithVars)

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using
  ( PFormula
  ; toFormula₂
  ; _∈PF_
  ; _≈PF_
  ; _⇒PF_
  ; _∧PF_
  ; _∨PF_
  ; _↔PF_
  ; ∀PF
  ; ∃PF
  ; toFormula
  )

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Term; Formula
  ; ⊥F; _∈F_; _≈F_; _⇒_; _∧F_; _∨F_; _↔F_; ∀F; ∃F
  )

private
  absurdNothingJust
    : ∀ {ℓA ℓB} {A : Set ℓA} {x : A} {B : Set ℓB}
    → nothing ≡ just x
    → B
  absurdNothingJust ()

toPFormulaWithVars-from-toPFormula
  : ∀ env φ p
  → toPFormula env φ ≡ just p
  → Σ (List ℕ) (λ vs → toPFormulaWithVars env φ ≡ just (p , vs))
toPFormulaWithVars-from-toPFormula env φ p h with toPFormulaWithVars env φ
... | nothing = absurdNothingJust h
... | just (p' , vs) with h
... | refl = (vs , refl)

-- `toFormula₂` is the shared helper behind all binary connectives in `toFormula`.
toFormula₂RoundTrip
  : ∀ {φ ψ}
  → (mk : Formula → Formula → Formula)
  → (p q : PFormula)
  → toFormula p ≡ just φ
  → toFormula q ≡ just ψ
  → toFormula₂ mk p q ≡ just (mk φ ψ)
toFormula₂RoundTrip mk p q hP hQ with toFormula p | hP
... | nothing | ()
... | just φ' | refl with toFormula q | hQ
... | nothing | ()
... | just ψ' | refl = refl

toPFormulaWithVarsMembershipInversion
  : ∀ env t u p vs
  → toPFormulaWithVars env (t ∈F u) ≡ just (p , vs)
  → Σ Term (λ t' →
    Σ Term (λ u' →
      termToToken env t ≡ just t' ×
      termToToken env u ≡ just u' ×
      p ≡ (t' ∈PF u')))
toPFormulaWithVarsMembershipInversion env t u p vs h
  with termToToken env t | termToToken env u
... | nothing | _ = absurdNothingJust h
... | just _ | nothing = absurdNothingJust h
... | just t' | just u' with h
... | refl = (t' , (u' , (refl , (refl , refl))))

toPFormulaWithVarsEqualityInversion
  : ∀ env t u p vs
  → toPFormulaWithVars env (t ≈F u) ≡ just (p , vs)
  → Σ Term (λ t' →
    Σ Term (λ u' →
      termToToken env t ≡ just t' ×
      termToToken env u ≡ just u' ×
      p ≡ (t' ≈PF u')))
toPFormulaWithVarsEqualityInversion env t u p vs h
  with termToToken env t | termToToken env u
... | nothing | _ = absurdNothingJust h
... | just _ | nothing = absurdNothingJust h
... | just t' | just u' with h
... | refl = (t' , (u' , (refl , (refl , refl))))

toPFormulaWithVarsImpInversion
  : ∀ env φ ψ p vs
  → toPFormulaWithVars env (φ ⇒ ψ) ≡ just (p , vs)
  → Σ (PFormula × List ℕ) (λ resφ →
    Σ (PFormula × List ℕ) (λ resψ →
      toPFormulaWithVars env φ ≡ just resφ ×
      toPFormulaWithVars env ψ ≡ just resψ ×
      p ≡ (fst resφ ⇒PF fst resψ)))
toPFormulaWithVarsImpInversion env φ ψ p vs h
  with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = absurdNothingJust h
... | just _ | nothing = absurdNothingJust h
... | just (pφ , vsφ) | just (pψ , vsψ) with h
... | refl = ((pφ , vsφ) , ((pψ , vsψ) , (refl , (refl , refl))))

toPFormulaWithVarsAndInversion
  : ∀ env φ ψ p vs
  → toPFormulaWithVars env (φ ∧F ψ) ≡ just (p , vs)
  → Σ (PFormula × List ℕ) (λ resφ →
    Σ (PFormula × List ℕ) (λ resψ →
      toPFormulaWithVars env φ ≡ just resφ ×
      toPFormulaWithVars env ψ ≡ just resψ ×
      p ≡ (fst resφ ∧PF fst resψ)))
toPFormulaWithVarsAndInversion env φ ψ p vs h
  with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = absurdNothingJust h
... | just _ | nothing = absurdNothingJust h
... | just (pφ , vsφ) | just (pψ , vsψ) with h
... | refl = ((pφ , vsφ) , ((pψ , vsψ) , (refl , (refl , refl))))

toPFormulaWithVarsOrInversion
  : ∀ env φ ψ p vs
  → toPFormulaWithVars env (φ ∨F ψ) ≡ just (p , vs)
  → Σ (PFormula × List ℕ) (λ resφ →
    Σ (PFormula × List ℕ) (λ resψ →
      toPFormulaWithVars env φ ≡ just resφ ×
      toPFormulaWithVars env ψ ≡ just resψ ×
      p ≡ (fst resφ ∨PF fst resψ)))
toPFormulaWithVarsOrInversion env φ ψ p vs h
  with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = absurdNothingJust h
... | just _ | nothing = absurdNothingJust h
... | just (pφ , vsφ) | just (pψ , vsψ) with h
... | refl = ((pφ , vsφ) , ((pψ , vsψ) , (refl , (refl , refl))))

toPFormulaWithVarsIffInversion
  : ∀ env φ ψ p vs
  → toPFormulaWithVars env (φ ↔F ψ) ≡ just (p , vs)
  → Σ (PFormula × List ℕ) (λ resφ →
    Σ (PFormula × List ℕ) (λ resψ →
      toPFormulaWithVars env φ ≡ just resφ ×
      toPFormulaWithVars env ψ ≡ just resψ ×
      p ≡ (fst resφ ↔PF fst resψ)))
toPFormulaWithVarsIffInversion env φ ψ p vs h
  with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = absurdNothingJust h
... | just _ | nothing = absurdNothingJust h
... | just (pφ , vsφ) | just (pψ , vsψ) with h
... | refl = ((pφ , vsφ) , ((pψ , vsψ) , (refl , (refl , refl))))

toPFormulaWithVarsForallInversion
  : ∀ env φ p vs
  → toPFormulaWithVars env (∀F φ) ≡ just (p , vs)
  → Σ (PFormula × List ℕ) (λ resφ →
    toPFormulaWithVars (fresh env ∷ env) φ ≡ just resφ ×
    p ≡ ∀PF (fresh env) (fst resφ))
toPFormulaWithVarsForallInversion env φ p vs h with toPFormulaWithVars (fresh env ∷ env) φ
... | nothing = absurdNothingJust h
... | just (pφ , vsφ) with h
... | refl = ((pφ , vsφ) , (refl , refl))

toPFormulaWithVarsExistsInversion
  : ∀ env φ p vs
  → toPFormulaWithVars env (∃F φ) ≡ just (p , vs)
  → Σ (PFormula × List ℕ) (λ resφ →
    toPFormulaWithVars (fresh env ∷ env) φ ≡ just resφ ×
    p ≡ ∃PF (fresh env) (fst resφ))
toPFormulaWithVarsExistsInversion env φ p vs h with toPFormulaWithVars (fresh env ∷ env) φ
... | nothing = absurdNothingJust h
... | just (pφ , vsφ) with h
... | refl = ((pφ , vsφ) , (refl , refl))
