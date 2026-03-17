{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Reify.WffReify where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  ; _++_
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using
  ( Sig
  ; tokLParen
  ; tokRParen
  ; tokImp
  ; tokAnd
  ; tokOr
  ; tokIff
  ; tokNot
  ; tokAll
  ; tokEx
  ; tokBot
  ; tokIn
  ; tokEq
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using
  ( PFormula
  ; metaF
  ; botF
  ; notPF
  ; _∈PF_
  ; _≈PF_
  ; _⇒PF_
  ; _∧PF_
  ; _∨PF_
  ; _↔PF_
  ; ∀PF
  ; ∃PF
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Reify.TermReify using (reifyTerm)
open import LogOS.Apps.ZFC.Proof.Syntax as ZF using (Term)

reifyWff : Sig → (env : List ℕ) → PFormula → Maybe (List ℕ)
reifyWff S env (metaF x) = just (x ∷ [])
reifyWff S env botF = just (tokBot S ∷ [])
reifyWff S env (notPF φ) with reifyWff S env φ
... | just xs = just (tokNot S ∷ xs)
... | nothing = nothing
reifyWff S env (t ∈PF u) with reifyTerm S env t
... | nothing = nothing
... | just xs with reifyTerm S env u
... | just ys = just (xs ++ (tokIn S ∷ ys))
... | nothing = nothing
reifyWff S env (t ≈PF u) with reifyTerm S env t
... | nothing = nothing
... | just xs with reifyTerm S env u
... | just ys = just (xs ++ (tokEq S ∷ ys))
... | nothing = nothing
reifyWff S env (φ ⇒PF ψ) with reifyWff S env φ
... | nothing = nothing
... | just xs with reifyWff S env ψ
... | just ys = just (tokLParen S ∷ (xs ++ (tokImp S ∷ ys)) ++ (tokRParen S ∷ []))
... | nothing = nothing
reifyWff S env (φ ∧PF ψ) with reifyWff S env φ
... | nothing = nothing
... | just xs with reifyWff S env ψ
... | just ys = just (tokLParen S ∷ (xs ++ (tokAnd S ∷ ys)) ++ (tokRParen S ∷ []))
... | nothing = nothing
reifyWff S env (φ ∨PF ψ) with reifyWff S env φ
... | nothing = nothing
... | just xs with reifyWff S env ψ
... | just ys = just (tokLParen S ∷ (xs ++ (tokOr S ∷ ys)) ++ (tokRParen S ∷ []))
... | nothing = nothing
reifyWff S env (φ ↔PF ψ) with reifyWff S env φ
... | nothing = nothing
... | just xs with reifyWff S env ψ
... | just ys = just (tokLParen S ∷ (xs ++ (tokIff S ∷ ys)) ++ (tokRParen S ∷ []))
... | nothing = nothing
reifyWff S env (∀PF x φ) with reifyWff S (x ∷ env) φ
... | just xs = just (tokAll S ∷ x ∷ xs)
... | nothing = nothing
reifyWff S env (∃PF x φ) with reifyWff S (x ∷ env) φ
... | just xs = just (tokEx S ∷ x ∷ xs)
... | nothing = nothing
