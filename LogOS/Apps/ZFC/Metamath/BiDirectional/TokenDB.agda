{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.TokenDB where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

import LogOS.Ports.Metamath as MM

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
      ; _>>=_
  ; Unit
  ; Fin
  ; fzero
  ; fsuc
  ; less
  ; equal
  ; greater
  ; cmpNat
  ; _++_
      ; mapMaybeList
  ; map
  ; dedup
  ; len
  ; reverse
  )

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Types using
  ( SupportFrame
  ; mkSupportFrame
  ; FormulaEntry
  ; mkFormulaEntry
  ; TokenEntry
  ; mkTokenEntry
  )

open SupportFrame
open FormulaEntry
open TokenEntry

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Reify using (toPFormulaWithVars)

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using
  ( Sig
  ; tcSet
  )
open import LogOS.Apps.ZFC.Metamath.SetMM.Reify.Provable using (reify⊢)

open import LogOS.Apps.ZFC.Metamath.Interpretation using (parseClosedConcl; interpretMetaFree)

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Term; Formula
  ; var; emptyT; pairT; unionT; powerT; succT; omegaT
  ; ⊥F; _∈F_; _≈F_; _⇒_; _∧F_; _∨F_; _↔F_; ∀F; ∃F
  )

normalizeMandatoryVars : List ℕ → List ℕ
normalizeMandatoryVars xs = reverse (dedup xs)

supportFrameFor : FormulaEntry → List ℕ → SupportFrame
supportFrameFor e binderVars =
  mkSupportFrame (vars e) binderVars (normalizeMandatoryVars (vars e ++ binderVars))

mandatoryFrameHyps : Sig → List ℕ → List (List ℕ)
mandatoryFrameHyps S frame = map (λ v → tcSet S ∷ v ∷ []) frame

tokenEntryHyps : Sig → TokenEntry → List (List ℕ)
tokenEntryHyps S e = mandatoryFrameHyps S (vars e)

-- Emit one DB row from one logical entry, keeping the support/frame split
-- explicit for callers that want to reason about the emitted mandatory frame.
toTokenEntryWithFrame : Sig → FormulaEntry → Maybe (TokenEntry × SupportFrame)
toTokenEntryWithFrame S e with toPFormulaWithVars (vars e) (formula e)
... | nothing = nothing
... | just (p , binderVars) with reify⊢ S (vars e ++ binderVars) p
... | nothing = nothing
... | just rowConcl =
  let
    frame = supportFrameFor e binderVars
  in
  just (mkTokenEntry (mandatoryVars frame) rowConcl , frame)

-- Emit one canonical DB row from one logical entry.
toTokenEntry : Sig → FormulaEntry → Maybe TokenEntry
toTokenEntry S e =
  toTokenEntryWithFrame S e >>= λ (row , _) →
  just row

-- Parse one token row back into a logical formula.
--
-- This follows the interpretation pipeline exactly: mandatory-frame closure
-- first, then meta-free interpretation and vacuous-binder normalization.
interpretTokenEntry : Sig → TokenEntry → Maybe Formula
interpretTokenEntry S e =
  parseClosedConcl S (tokenEntryHyps S e) (concl e) >>= interpretMetaFree

-- Build token rows together with their explicit support/frame witnesses.
buildEntriesWithFrames : Sig → List FormulaEntry → Maybe (List (TokenEntry × SupportFrame))
buildEntriesWithFrames S es = mapMaybeList (toTokenEntryWithFrame S) es

-- Build token rows from logical entries.
buildEntries : Sig → List FormulaEntry → Maybe (List TokenEntry)
buildEntries S es =
  buildEntriesWithFrames S es >>= λ rows →
  just (map fst rows)

-- Package rows into a proper database with automatic metavariable-like
-- set-variable hypotheses (`(setvar)` in DB style).
--
-- The resulting DB is meant to be interpreted through `Interpretation.DB`,
-- which applies the same closure + normalization pipeline as
-- `interpretTokenEntry`.
mkTokenDB : Sig → List FormulaEntry → Maybe (MM.Database (List ℕ))
mkTokenDB S es with buildEntries S es
... | nothing = nothing
... | just rows =
  just
    (record
      { Label = Fin (len rows)
      ; hyps = projectHyps rows
      ; concl = projectConcl rows
      })
  where
    projectAt : ∀ {A} → (TokenEntry → A) → (ys : List TokenEntry) → Fin (len ys) → A
    projectAt _ [] ()
    projectAt f (e ∷ es) fzero = f e
    projectAt f (e ∷ es) (fsuc i) = projectAt f es i

    projectHyps : (ys : List TokenEntry) → Fin (len ys) → List (List ℕ)
    projectHyps ys i = projectAt (tokenEntryHyps S) ys i

    projectConcl : (ys : List TokenEntry) → Fin (len ys) → List ℕ
    projectConcl ys i = projectAt concl ys i

isClosedTerm : ℕ → Term → Maybe Unit
isClosedTerm depth (var n) with cmpNat n depth
... | less = just tt
... | equal = nothing
... | greater = nothing
isClosedTerm _ emptyT = just tt
isClosedTerm _ (pairT _ _) = nothing
isClosedTerm depth (unionT t) = isClosedTerm depth t
isClosedTerm depth (powerT t) = isClosedTerm depth t
isClosedTerm depth (succT t) = isClosedTerm depth t
isClosedTerm _ omegaT = just tt

isClosedFormula : Formula → Maybe Unit
isClosedFormula φ = isClosedFormula' zero φ
  where
    isClosedFormula' : ℕ → Formula → Maybe Unit
    isClosedFormula' d (t ∈F u) =
      isClosedTerm d t >>= λ _ → isClosedTerm d u
    isClosedFormula' d (t ≈F u) =
      isClosedTerm d t >>= λ _ → isClosedTerm d u
    isClosedFormula' d (φ ⇒ ψ) =
      isClosedFormula' d φ >>= λ _ → isClosedFormula' d ψ
    isClosedFormula' d (φ ∧F ψ) =
      isClosedFormula' d φ >>= λ _ → isClosedFormula' d ψ
    isClosedFormula' d (φ ∨F ψ) =
      isClosedFormula' d φ >>= λ _ → isClosedFormula' d ψ
    isClosedFormula' d (φ ↔F ψ) =
      isClosedFormula' d φ >>= λ _ → isClosedFormula' d ψ
    isClosedFormula' d (∀F φ) = isClosedFormula' (suc d) φ
    isClosedFormula' d (∃F φ) = isClosedFormula' (suc d) φ
    isClosedFormula' _ ⊥F = just tt

-- Construct a closed logical entry when possible.
mkClosedFormulaEntry : Formula → Maybe FormulaEntry
mkClosedFormulaEntry φ with isClosedFormula φ
... | nothing = nothing
... | just _ = just (mkFormulaEntry [] φ)

collectClosedEntries : List Formula → Maybe (List FormulaEntry)
collectClosedEntries fs = mapMaybeList mkClosedFormulaEntry fs

-- Convenience for closed lists of formulas.
mkClosedTokenDB : Sig → List Formula → Maybe (MM.Database (List ℕ))
mkClosedTokenDB S fs = collectClosedEntries fs >>= mkTokenDB S
