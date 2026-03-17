{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.Rename where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
      ; _>>=_
  )

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Env using (fresh; termToToken)

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Term; Formula
  ; var; emptyT; pairT; unionT; powerT; succT; omegaT
  ; ⊥F; _∈F_; _≈F_; _⇒_; _∧F_; _∨F_; _↔F_; ∀F; ∃F
  )

-- Transport a formula by the same environment threading used by `toPFormula`.
--
-- This is not a pure de Bruijn-preserving rename in the `renameFormula` sense;
-- it is the exact environment-index transport that `toPFormula`+`toFormula`
-- computes.

renameTermByEnv : ∀ env → Term → Term
renameTermByEnv env (var n) with termToToken env (var n)
... | just t = t
... | nothing = var n
renameTermByEnv env emptyT = emptyT
renameTermByEnv env (pairT t u) = pairT (renameTermByEnv env t) (renameTermByEnv env u)
renameTermByEnv env (unionT t) = unionT (renameTermByEnv env t)
renameTermByEnv env (powerT t) = powerT (renameTermByEnv env t)
renameTermByEnv env (succT t) = succT (renameTermByEnv env t)
renameTermByEnv env omegaT = omegaT

data Inspect {ℓ : Level} {A : Set ℓ} (x : A) : Set ℓ where
  witness : (y : A) → x ≡ y → Inspect x

inspect : ∀ {ℓ : Level} {A : Set ℓ} (x : A) → Inspect x
inspect x = witness x refl

renameTermByEnv-fromTermToToken
  : ∀ env t t' → termToToken env t ≡ just t' → renameTermByEnv env t ≡ t'
renameTermByEnv-fromTermToToken env (var n) t' h with termToToken env (var n) | h
... | just t'' | LogOS.Prelude.refl = LogOS.Prelude.refl
... | nothing | ()
renameTermByEnv-fromTermToToken env emptyT .emptyT LogOS.Prelude.refl =
  LogOS.Prelude.refl
renameTermByEnv-fromTermToToken env (pairT _ _) t' ()
renameTermByEnv-fromTermToToken env (unionT t) t' h
  with inspect (termToToken env t)
... | witness mt eq =
  go mt eq (subst (λ mt' → (mt' >>= λ u → just (unionT u)) ≡ just t') eq h)
  where
    go
      : (mt' : Core.Maybe Term)
      → termToToken env t ≡ mt'
      → (mt' >>= λ u → just (unionT u)) ≡ just t'
      → renameTermByEnv env (unionT t) ≡ t'
    go Core.nothing _ ()
    go (Core.just t'') eq' LogOS.Prelude.refl =
      cong unionT (renameTermByEnv-fromTermToToken env t t'' eq')
renameTermByEnv-fromTermToToken env (powerT t) t' h
  with inspect (termToToken env t)
... | witness mt eq =
  go mt eq (subst (λ mt' → (mt' >>= λ u → just (powerT u)) ≡ just t') eq h)
  where
    go
      : (mt' : Core.Maybe Term)
      → termToToken env t ≡ mt'
      → (mt' >>= λ u → just (powerT u)) ≡ just t'
      → renameTermByEnv env (powerT t) ≡ t'
    go Core.nothing _ ()
    go (Core.just t'') eq' LogOS.Prelude.refl =
      cong powerT (renameTermByEnv-fromTermToToken env t t'' eq')
renameTermByEnv-fromTermToToken env (succT t) t' h
  with inspect (termToToken env t)
... | witness mt eq =
  go mt eq (subst (λ mt' → (mt' >>= λ u → just (succT u)) ≡ just t') eq h)
  where
    go
      : (mt' : Core.Maybe Term)
      → termToToken env t ≡ mt'
      → (mt' >>= λ u → just (succT u)) ≡ just t'
      → renameTermByEnv env (succT t) ≡ t'
    go Core.nothing _ ()
    go (Core.just t'') eq' LogOS.Prelude.refl =
      cong succT (renameTermByEnv-fromTermToToken env t t'' eq')
renameTermByEnv-fromTermToToken env omegaT .omegaT LogOS.Prelude.refl =
  LogOS.Prelude.refl

renameFormulaByEnv : ∀ env → Formula → Formula
renameFormulaByEnv _ ⊥F = ⊥F
renameFormulaByEnv env (t ∈F u) = renameTermByEnv env t ∈F renameTermByEnv env u
renameFormulaByEnv env (t ≈F u) = renameTermByEnv env t ≈F renameTermByEnv env u
renameFormulaByEnv env (φ ⇒ ψ) = renameFormulaByEnv env φ ⇒ renameFormulaByEnv env ψ
renameFormulaByEnv env (φ ∧F ψ) = renameFormulaByEnv env φ ∧F renameFormulaByEnv env ψ
renameFormulaByEnv env (φ ∨F ψ) = renameFormulaByEnv env φ ∨F renameFormulaByEnv env ψ
renameFormulaByEnv env (φ ↔F ψ) = renameFormulaByEnv env φ ↔F renameFormulaByEnv env ψ
renameFormulaByEnv env (∀F φ) =
  let x = fresh env in
  ∀F (renameFormulaByEnv (x ∷ env) φ)
renameFormulaByEnv env (∃F φ) =
  let x = fresh env in
  ∃F (renameFormulaByEnv (x ∷ env) φ)
