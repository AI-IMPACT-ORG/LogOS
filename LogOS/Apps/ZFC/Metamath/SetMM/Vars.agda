{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Vars where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; contains
  ; Cmp
  ; cmpNat
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using (Sig; tcWff; tcSet)

record Vars : Set where
  field
    wffVars : List ℕ
    setVars : List ℕ

open Vars public

data VarHyp : Set where
  varWffVar : VarHyp
  varSetVar : VarHyp
  varNoVar : VarHyp

classifyVarHyp : Sig → ℕ → VarHyp
classifyVarHyp S tc = goWff (cmpNat tc (tcWff S))
  where
    goWff : Cmp → VarHyp
    goSet : Cmp → VarHyp

    goWff Core.equal = varWffVar
    goWff Core.less = goSet (cmpNat tc (tcSet S))
    goWff Core.greater = goSet (cmpNat tc (tcSet S))

    goSet Core.equal = varSetVar
    goSet Core.less = varNoVar
    goSet Core.greater = varNoVar

-- Extract (wff/set) variable tokens from a Metamath mandatory-frame list.
--
-- Mandatory `$f` hypotheses are stored as two-symbol formulas: `[typecode, var]`.
varsFromHyps : Sig → List (List ℕ) → Maybe Vars
varsFromHyps S hs = go hs (record { wffVars = [] ; setVars = [] })
  where
    addFresh : ℕ → List ℕ → List ℕ → Maybe (List ℕ)
    addFresh x xs ys with contains x xs
    ... | just _ = nothing
    ... | nothing with contains x ys
    ... | just _ = nothing
    ... | nothing = just (x ∷ xs)

    go : List (List ℕ) → Vars → Maybe Vars
    go [] V = just V
    go ([] ∷ _) _ = nothing
    go ((tc ∷ []) ∷ _) _ = nothing
    go ((tc ∷ _ ∷ _ ∷ _) ∷ _) _ = nothing
    go ((tc ∷ v ∷ []) ∷ rest) V with classifyVarHyp S tc
    go ((tc ∷ v ∷ []) ∷ rest) V | varWffVar with addFresh v (wffVars V) (setVars V)
    ... | nothing = nothing
    ... | just xs = go rest (record { wffVars = xs ; setVars = setVars V })
    go ((tc ∷ v ∷ []) ∷ rest) V | varSetVar with addFresh v (setVars V) (wffVars V)
    ... | nothing = nothing
    ... | just xs = go rest (record { wffVars = wffVars V ; setVars = xs })
    go ((tc ∷ v ∷ []) ∷ rest) V | varNoVar = nothing

