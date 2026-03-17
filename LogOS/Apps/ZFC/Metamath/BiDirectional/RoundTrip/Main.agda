{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip.Main where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  )

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Env using (fresh)
open import LogOS.Apps.ZFC.Metamath.BiDirectional.Reify using (toPFormula; toPFormulaWithVars)
open import LogOS.Apps.ZFC.Metamath.BiDirectional.Rename using
  ( renameFormulaByEnv
  ; renameTermByEnv-fromTermToToken
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using
  ( PFormula
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

open import LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip.ReifyInversion using
  ( toPFormulaWithVars-from-toPFormula
  ; toFormula₂RoundTrip
  ; toPFormulaWithVarsMembershipInversion
  ; toPFormulaWithVarsEqualityInversion
  ; toPFormulaWithVarsImpInversion
  ; toPFormulaWithVarsAndInversion
  ; toPFormulaWithVarsOrInversion
  ; toPFormulaWithVarsIffInversion
  ; toPFormulaWithVarsForallInversion
  ; toPFormulaWithVarsExistsInversion
  )

-- Main renaming roundtrip lemma stated on the single-traversal reifier.
toFormulaRoundTripWithVars
  : ∀ env φ p vs
  → toPFormulaWithVars env φ ≡ just (p , vs)
  → toFormula p ≡ just (renameFormulaByEnv env φ)
toFormulaRoundTripWithVars env ⊥F p vs refl = refl
toFormulaRoundTripWithVars env (t ∈F u) p vs h
  with toPFormulaWithVarsMembershipInversion env t u p vs h
... | (t' , (u' , (ht , (hu , hp)))) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (t ∈F u)))
    (sym hp)
    (cong
      just
      (cong₂
        _∈F_
        (sym (renameTermByEnv-fromTermToToken env t t' ht))
        (sym (renameTermByEnv-fromTermToToken env u u' hu))))
toFormulaRoundTripWithVars env (t ≈F u) p vs h
  with toPFormulaWithVarsEqualityInversion env t u p vs h
... | (t' , (u' , (ht , (hu , hp)))) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (t ≈F u)))
    (sym hp)
    (cong
      just
      (cong₂
        _≈F_
        (sym (renameTermByEnv-fromTermToToken env t t' ht))
        (sym (renameTermByEnv-fromTermToToken env u u' hu))))
toFormulaRoundTripWithVars env (φ ⇒ ψ) p vs h
  with toPFormulaWithVarsImpInversion env φ ψ p vs h
... | (resφ , (resψ , (hφ , (hψ , hp)))) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (φ ⇒ ψ)))
    (sym hp)
    (toFormula₂RoundTrip
      (λ p q → p ⇒ q)
      (fst resφ)
      (fst resψ)
      (toFormulaRoundTripWithVars env φ (fst resφ) (snd resφ) hφ)
      (toFormulaRoundTripWithVars env ψ (fst resψ) (snd resψ) hψ))
toFormulaRoundTripWithVars env (φ ∧F ψ) p vs h
  with toPFormulaWithVarsAndInversion env φ ψ p vs h
... | (resφ , (resψ , (hφ , (hψ , hp)))) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (φ ∧F ψ)))
    (sym hp)
    (toFormula₂RoundTrip
      (λ p q → p ∧F q)
      (fst resφ)
      (fst resψ)
      (toFormulaRoundTripWithVars env φ (fst resφ) (snd resφ) hφ)
      (toFormulaRoundTripWithVars env ψ (fst resψ) (snd resψ) hψ))
toFormulaRoundTripWithVars env (φ ∨F ψ) p vs h
  with toPFormulaWithVarsOrInversion env φ ψ p vs h
... | (resφ , (resψ , (hφ , (hψ , hp)))) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (φ ∨F ψ)))
    (sym hp)
    (toFormula₂RoundTrip
      (λ p q → p ∨F q)
      (fst resφ)
      (fst resψ)
      (toFormulaRoundTripWithVars env φ (fst resφ) (snd resφ) hφ)
      (toFormulaRoundTripWithVars env ψ (fst resψ) (snd resψ) hψ))
toFormulaRoundTripWithVars env (φ ↔F ψ) p vs h
  with toPFormulaWithVarsIffInversion env φ ψ p vs h
... | (resφ , (resψ , (hφ , (hψ , hp)))) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (φ ↔F ψ)))
    (sym hp)
    (toFormula₂RoundTrip
      (λ p q → p ↔F q)
      (fst resφ)
      (fst resψ)
      (toFormulaRoundTripWithVars env φ (fst resφ) (snd resφ) hφ)
      (toFormulaRoundTripWithVars env ψ (fst resψ) (snd resψ) hψ))
toFormulaRoundTripWithVars env (∀F φ) p vs h
  with toPFormulaWithVarsForallInversion env φ p vs h
... | (resφ , (hφ , hp)) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (∀F φ)))
    (sym hp)
    (go (toFormulaRoundTripWithVars (fresh env ∷ env) φ (fst resφ) (snd resφ) hφ))
  where
    go
      : toFormula (fst resφ)
        ≡ just (renameFormulaByEnv (fresh env ∷ env) φ)
      → toFormula (∀PF (fresh env) (fst resφ))
        ≡ just (renameFormulaByEnv env (∀F φ))
    go sub with toFormula (fst resφ) | sub
    ... | nothing | ()
    ... | just _ | refl = refl
toFormulaRoundTripWithVars env (∃F φ) p vs h
  with toPFormulaWithVarsExistsInversion env φ p vs h
... | (resφ , (hφ , hp)) =
  subst
    (λ r → toFormula r ≡ just (renameFormulaByEnv env (∃F φ)))
    (sym hp)
    (go (toFormulaRoundTripWithVars (fresh env ∷ env) φ (fst resφ) (snd resφ) hφ))
  where
    go
      : toFormula (fst resφ)
        ≡ just (renameFormulaByEnv (fresh env ∷ env) φ)
      → toFormula (∃PF (fresh env) (fst resφ))
        ≡ just (renameFormulaByEnv env (∃F φ))
    go sub with toFormula (fst resφ) | sub
    ... | nothing | ()
    ... | just _ | refl = refl

toFormulaRoundTrip
  : ∀ env φ p
  → toPFormula env φ ≡ just p
  → toFormula p ≡ just (renameFormulaByEnv env φ)
toFormulaRoundTrip env φ p h =
  let
    (vs , hv) = toPFormulaWithVars-from-toPFormula env φ p h
  in
  toFormulaRoundTripWithVars env φ p vs hv

toFormulaRenamingRoundTripWithVars
  : ∀ env φ p vs
  → toPFormulaWithVars env φ ≡ just (p , vs)
  → toFormula p ≡ just (renameFormulaByEnv env φ)
toFormulaRenamingRoundTripWithVars = toFormulaRoundTripWithVars

toFormulaRenamingRoundTrip
  : ∀ env φ p
  → toPFormula env φ ≡ just p
  → toFormula p ≡ just (renameFormulaByEnv env φ)
toFormulaRenamingRoundTrip = toFormulaRoundTrip
