{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Interpretation.Close where

-- Closing Metamath’s implicit outer ∀-quantification over set variables.
--
-- Metamath statements are implicitly universally quantified over *all* variables.
-- In Set.MM, the object language already has explicit quantifiers (`A.` / `E.`),
-- but free set variables in a theorem/axiom are still implicitly ∀ at the meta-level.
--
-- We make that boundary explicit by prefixing `A. x` for every set-variable token
-- in the mandatory frame (derived from `$f` hypotheses).
--
-- This may introduce redundant (vacuous) binders (e.g. when a variable is already
-- quantified in the object language). We normalize those away later.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; cmpNat
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using
  ( Sig
  ; tokAll
  ; tc⊢
  )

prefixAllSets : Sig → List ℕ → List ℕ → List ℕ
prefixAllSets S [] body = body
prefixAllSets S (xTok ∷ xs) body =
  tokAll S ∷ xTok ∷ prefixAllSets S xs body

-- Expect a full provable statement token list: `|- <wff>`.
close⊢Tokens : Sig → List ℕ → List ℕ → Maybe (List ℕ)
close⊢Tokens S allSetVars [] = nothing
close⊢Tokens S allSetVars (tc ∷ body) with cmpNat tc (tc⊢ S)
... | Core.equal = just (tc ∷ prefixAllSets S allSetVars body)
... | Core.less = nothing
... | Core.greater = nothing
