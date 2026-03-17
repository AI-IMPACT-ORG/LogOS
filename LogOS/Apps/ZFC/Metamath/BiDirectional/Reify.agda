{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.Reify where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
      ; _>>=_
  ; _++_
  )

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Env using (fresh; termToToken)

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using
  ( PFormula
  ; botF
  ; _∈PF_
  ; _≈PF_
  ; _⇒PF_
  ; _∧PF_
  ; _∨PF_
  ; _↔PF_
  ; ∀PF
  ; ∃PF
  )

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Formula
  ; ⊥F; _∈F_; _≈F_; _⇒_; _∧F_; _∨F_; _↔F_; ∀F; ∃F
  )

-- Reify a formula under an environment, additionally returning the set-variable
-- tokens introduced by quantifiers.
--
-- This is used to satisfy the mandatory-frame check when emitting Metamath rows.
toPFormulaWithVars : List ℕ → Formula → Maybe (PFormula × List ℕ)
toPFormulaWithVars env ⊥F = just (botF , [])
toPFormulaWithVars env (t ∈F u) with termToToken env t | termToToken env u
... | just xs | just ys = just (xs ∈PF ys , [])
... | nothing | _ = nothing
... | just _ | nothing = nothing
toPFormulaWithVars env (t ≈F u) with termToToken env t | termToToken env u
... | just xs | just ys = just (xs ≈PF ys , [])
... | nothing | _ = nothing
... | just _ | nothing = nothing
toPFormulaWithVars env (φ ⇒ ψ) with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just (p , vs) | just (q , ws) = just (p ⇒PF q , vs ++ ws)
toPFormulaWithVars env (φ ∧F ψ) with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just (p , vs) | just (q , ws) = just (p ∧PF q , vs ++ ws)
toPFormulaWithVars env (φ ∨F ψ) with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just (p , vs) | just (q , ws) = just (p ∨PF q , vs ++ ws)
toPFormulaWithVars env (φ ↔F ψ) with toPFormulaWithVars env φ | toPFormulaWithVars env ψ
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just (p , vs) | just (q , ws) = just (p ↔PF q , vs ++ ws)
toPFormulaWithVars env (∀F φ) =
  let x = fresh env in
  toPFormulaWithVars (x ∷ env) φ >>= λ (p , vs) →
  just (∀PF x p , x ∷ vs)
toPFormulaWithVars env (∃F φ) =
  let x = fresh env in
  toPFormulaWithVars (x ∷ env) φ >>= λ (p , vs) →
  just (∃PF x p , x ∷ vs)

-- Reify one formula under an explicit variable environment into `PFormula`.
toPFormula : List ℕ → Formula → Maybe PFormula
toPFormula env φ =
  toPFormulaWithVars env φ >>= λ (p , _) →
  just p
