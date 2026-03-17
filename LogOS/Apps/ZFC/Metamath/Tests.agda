{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Tests where

-- Smoke test for the Metamath emission path:
--   Formula -> DB token row -> parsed formula
-- should preserve quantified structure.

open import LogOS.Prelude using
  ( ℕ
  ; _×_
  ; _≡_
  ; snd
  ; refl
  )
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using (Sig)
open import LogOS.Apps.ZFC.Metamath.BiDirectional using
  ( SupportFrame
  ; FormulaEntry
  ; TokenEntry
  ; mkFormulaEntry
  ; mkClosedFormulaEntry
  ; toTokenEntryWithFrame
  ; toTokenEntry
  ; tokenEntryHyps
  ; interpretTokenEntry
  )
open SupportFrame
open TokenEntry

import LogOS.Apps.ZFC.Metamath.Interpretation.DB as DBInterp
import LogOS.Ports.Metamath as MM
open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Formula
  ; var
  ; ⊥F
  ; _∈F_
  ; ∀F
  ; emptyT; pairT
  ; unionT
  ; omegaT
  ; succT
  )
open import LogOS.Apps.ZFC.Metamath.Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  ; fzero
  ; fsuc
  )

-- Concrete signature with disjoint token indices.
testSig : Sig

testSig =
  record
    { tc⊢ = 100
    ; tcWff = 101
    ; tcSet = 102
    ; tokLParen = 103 ; tokRParen = 104
    ; tokImp = 105 ; tokAnd = 106 ; tokOr = 107 ; tokIff = 108
    ; tokNot = 109 ; tokAll = 110 ; tokEx = 111
    ; tokBot = 114
    ; tokEmpty = 115 ; tokOmega = 116
    ; tokUnion = 117 ; tokPower = 118 ; tokSucc = 119
    ; tokPair = 120
    ; tokIn = 112 ; tokEq = 113
    }

testFormula : Formula

testFormula = ∀F (var 0 ∈F var 0)

botFormula : Formula

botFormula = ⊥F

termFormula : Formula

termFormula = succT (unionT emptyT) ∈F omegaT

unsupportedPairFormula : Formula

unsupportedPairFormula = pairT emptyT emptyT ∈F omegaT

testEntry : Maybe FormulaEntry

testEntry = mkClosedFormulaEntry testFormula

botEntry : Maybe FormulaEntry

botEntry = mkClosedFormulaEntry botFormula

termEntry : Maybe FormulaEntry

termEntry = mkClosedFormulaEntry termFormula

frameAmbient : {A : Set} → A × SupportFrame → List ℕ
frameAmbient q = ambientVars (snd q)

frameBinders : {A : Set} → A × SupportFrame → List ℕ
frameBinders q = binderVars (snd q)

frameMandatory : {A : Set} → A × SupportFrame → List ℕ
frameMandatory q = mandatoryVars (snd q)

singletonRowDBInterpret : TokenEntry → Maybe Formula
singletonRowDBInterpret row =
  let
    DB : MM.Database (List ℕ)
    DB =
      record
        { Label = LogOS.Apps.ZFC.Metamath.Core.Fin 1
        ; hyps = λ { fzero → tokenEntryHyps testSig row }
        ; concl = λ { fzero → concl row }
        }
    module D = DBInterp.ForDB testSig DB
  in
  D.interpretConcl fzero

twoRowDBInterpret₁ : TokenEntry → TokenEntry → Maybe Formula
twoRowDBInterpret₁ row₀ row₁ =
  let
    DB : MM.Database (List ℕ)
    DB =
      record
        { Label = LogOS.Apps.ZFC.Metamath.Core.Fin 2
        ; hyps = λ
            { fzero        → tokenEntryHyps testSig row₀
            ; (fsuc fzero) → tokenEntryHyps testSig row₁
            }
        ; concl = λ
            { fzero        → concl row₀
            ; (fsuc fzero) → concl row₁
            }
        }
    module D = DBInterp.ForDB testSig DB
  in
  D.interpretConcl fzero

twoRowDBInterpret₂ : TokenEntry → TokenEntry → Maybe Formula
twoRowDBInterpret₂ row₀ row₁ =
  let
    DB : MM.Database (List ℕ)
    DB =
      record
        { Label = LogOS.Apps.ZFC.Metamath.Core.Fin 2
        ; hyps = λ
            { fzero        → tokenEntryHyps testSig row₀
            ; (fsuc fzero) → tokenEntryHyps testSig row₁
            }
        ; concl = λ
            { fzero        → concl row₀
            ; (fsuc fzero) → concl row₁
            }
        }
    module D = DBInterp.ForDB testSig DB
  in
  D.interpretConcl (fsuc fzero)

testFrameAmbientSupport :
  (testEntry >>= λ e → toTokenEntryWithFrame testSig e >>= λ q → just (frameAmbient q))
  ≡ just []
testFrameAmbientSupport = refl

testFrameBinderSupport :
  (testEntry >>= λ e → toTokenEntryWithFrame testSig e >>= λ q → just (frameBinders q))
  ≡ just (1 ∷ [])
testFrameBinderSupport = refl

testFrameMandatorySupport :
  (testEntry >>= λ e → toTokenEntryWithFrame testSig e >>= λ q → just (frameMandatory q))
  ≡ just (1 ∷ [])
testFrameMandatorySupport = refl

unsupportedPairEmission :
  toTokenEntry testSig (mkFormulaEntry [] unsupportedPairFormula) ≡ nothing
unsupportedPairEmission = refl

-- This forces one concrete quantified formula to be emitted and re-parsed.
-- A full compile-time `rfl` check certifies the path is live and coherent.
metamathEmissionRoundtrip :
  (testEntry >>= λ e → toTokenEntry testSig e >>= interpretTokenEntry testSig) ≡ just testFormula
metamathEmissionRoundtrip = refl

botEmissionRoundtrip :
  (botEntry >>= λ e → toTokenEntry testSig e >>= interpretTokenEntry testSig) ≡ just botFormula
botEmissionRoundtrip = refl

termFormulaEmissionRoundtrip :
  (termEntry >>= λ e → toTokenEntry testSig e >>= interpretTokenEntry testSig) ≡ just termFormula
termFormulaEmissionRoundtrip = refl

singletonDBEmissionRoundtrip :
  (testEntry >>= λ e → toTokenEntry testSig e >>= singletonRowDBInterpret)
  ≡ just testFormula
singletonDBEmissionRoundtrip = refl

twoRowDBEmissionRoundtrip₁ :
  (botEntry >>= λ e₀ → toTokenEntry testSig e₀ >>= λ row₀ →
   testEntry >>= λ e₁ → toTokenEntry testSig e₁ >>= λ row₁ →
   twoRowDBInterpret₁ row₀ row₁)
  ≡ just botFormula
twoRowDBEmissionRoundtrip₁ = refl

twoRowDBEmissionRoundtrip₂ :
  (botEntry >>= λ e₀ → toTokenEntry testSig e₀ >>= λ row₀ →
   testEntry >>= λ e₁ → toTokenEntry testSig e₁ >>= λ row₁ →
   twoRowDBInterpret₂ row₀ row₁)
  ≡ just testFormula
twoRowDBEmissionRoundtrip₂ = refl
