{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Reify.TermReify where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  ; _++_
  ; lookupAt
  ; lookupIx
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using
  ( Sig
  ; tokEmpty
  ; tokOmega
  ; tokUnion
  ; tokPower
  ; tokSucc
  )

open import LogOS.Apps.ZFC.Proof.Syntax as ZF using
  ( Term
  ; var
  ; emptyT
  ; pairT
  ; unionT
  ; powerT
  ; succT
  ; omegaT
  )

lookupEnvTok : ℕ → List ℕ → Maybe ℕ
lookupEnvTok = lookupIx

reifyTerm : Sig → (env : List ℕ) → Term → Maybe (List ℕ)
reifyTerm S env (ZF.var n) with lookupAt n env
... | nothing = nothing
... | just x = just (x ∷ [])
reifyTerm S env (ZF.emptyT) = just (tokEmpty S ∷ [])
reifyTerm S env (ZF.pairT t u) = nothing
reifyTerm S env (ZF.unionT t) with reifyTerm S env t
... | nothing = nothing
... | just xs = just (tokUnion S ∷ xs)
reifyTerm S env (ZF.powerT t) with reifyTerm S env t
... | nothing = nothing
... | just xs = just (tokPower S ∷ xs)
reifyTerm S env (ZF.succT t) with reifyTerm S env t
... | nothing = nothing
... | just xs = just (tokSucc S ∷ xs)
reifyTerm S env ZF.omegaT = just (tokOmega S ∷ [])
