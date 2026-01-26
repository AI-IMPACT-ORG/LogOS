{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.QuantumCircuitAmp where

open import LogOS.Prelude

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.Fin using (Fin; fzero)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp as QCA
open import LogOS.Domain.UniversalIR.Quantum.Scalars.Free using (formalScalars)

module A = QCA.For formalScalars
open QCA.QScalars formalScalars
  renaming (_+_ to _+S_; _*_ to _*S_; -_ to negS; invSqrt2 to invSqrt2S)
open A using
  ( State; Wires; QCInstrP; QuantumCircuitAmpPCode; mkQCAP
  ; state
  ; QH; QX; QMEASURE; QCHALT
  ; stepQCAProb; pureDist
  ; applyInstr; setPCQCAP; setStateQCAP
  ; DistList; observeDistList
  ; probFalse; probTrue; collapseFalseRaw; collapseTrueRaw
  )

-- Example: one-qubit superposition then measurement, using formal scalars.

ket0 : State 1
ket0 (A._∷_ false A.[]) = 1#
ket0 (A._∷_ true A.[]) = 0#

progHM : List (QCInstrP 1)
progHM = QH fzero ∷ QMEASURE fzero 2 2 ∷ QCHALT ∷ []

q0 : QuantumCircuitAmpPCode 1
q0 = mkQCAP 0 ket0 progHM

qAfterH : QuantumCircuitAmpPCode 1
qAfterH =
  setPCQCAP 1 (setStateQCAP (applyInstr (QH fzero) ket0) q0)

distAfterH : DistList (QuantumCircuitAmpPCode 1)
distAfterH = stepQCAProb q0

distAfterH≡pure : distAfterH ≡ pureDist qAfterH
distAfterH≡pure = refl

measureBranches : DistList (QuantumCircuitAmpPCode 1)
measureBranches = stepQCAProb qAfterH

measureBranches-def :
  measureBranches ≡
    record
      { support =
          (probFalse fzero (state qAfterH)
          , setPCQCAP 2 (setStateQCAP (collapseFalseRaw fzero (state qAfterH)) qAfterH))
          ∷ (probTrue fzero (state qAfterH)
          , setPCQCAP 2 (setStateQCAP (collapseTrueRaw fzero (state qAfterH)) qAfterH))
          ∷ []
      }
measureBranches-def = refl

observedAfterMeasure : DistList (Wires 1)
observedAfterMeasure = observeDistList measureBranches

-- Example: two-qubit interference on the first wire (second wire is spectator).

ket00 : State 2
ket00 (A._∷_ false (A._∷_ false A.[])) = 1#
ket00 (A._∷_ false (A._∷_ true A.[])) = 0#
ket00 (A._∷_ true (A._∷_ false A.[])) = 0#
ket00 (A._∷_ true (A._∷_ true A.[])) = 0#

progHXH : List (QCInstrP 2)
progHXH = QH fzero ∷ QX fzero ∷ QH fzero ∷ QCHALT ∷ []

qHXH : QuantumCircuitAmpPCode 2
qHXH = mkQCAP 0 ket00 progHXH

stateHXH : State 2
stateHXH = applyInstr (QH fzero) (applyInstr (QX fzero) (applyInstr (QH fzero) ket00))

amp10-interference :
  stateHXH (A._∷_ true (A._∷_ false A.[])) ≡
    invSqrt2S *S (invSqrt2S *S (1# +S negS 0#) +S negS (invSqrt2S *S (1# +S 0#)))
amp10-interference = refl
