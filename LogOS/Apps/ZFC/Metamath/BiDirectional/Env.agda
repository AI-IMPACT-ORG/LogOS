{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.Env where

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
      ; _>>=_
  ; less
  ; equal
  ; greater
  ; cmpNat
  ; lookupAt
  )

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Term
  ; var; emptyT; pairT; unionT; powerT; succT; omegaT
  )

-- Pick a fresh token not currently in the environment.
--
-- A robust, terminating choice is `max(vars)+1`, guaranteed not to clash with
-- any existing token in `env`.
maxToken : List ℕ → ℕ
maxToken [] = zero
maxToken (x ∷ xs) with maxToken xs
... | m with cmpNat x m
... | less = m
... | equal = x
... | greater = x

fresh : List ℕ → ℕ
fresh env = suc (maxToken env)

-- A conservative term projection used when serializing formulas.
termToToken : List ℕ → Term → Maybe Term
termToToken env (var n) with lookupAt n env
... | nothing = nothing
... | just t = just (var t)
termToToken env emptyT = just emptyT
termToToken env (pairT _ _) = nothing
termToToken env (unionT t) = termToToken env t >>= λ u → just (unionT u)
termToToken env (powerT t) = termToToken env t >>= λ u → just (powerT u)
termToToken env (succT t) = termToToken env t >>= λ u → just (succT u)
termToToken env omegaT = just omegaT
