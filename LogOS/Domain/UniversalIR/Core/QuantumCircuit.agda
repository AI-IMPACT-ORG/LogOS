{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.QuantumCircuit where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core.Utils

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)

-- 5) Basis-state quantum circuits (explicit gates, deterministic measurement) -

not : Bool → Bool
not true  = false
not false = true

updateAt : ∀ {A : Set} → ℕ → (A → A) → List A → List A
updateAt _       _ []       = []
updateAt zero    f (x ∷ xs) = f x ∷ xs
updateAt (suc i) f (x ∷ xs) = x ∷ updateAt i f xs

data QCInstr : Set where
  QCHALT   : QCInstr
  QNOP     : QCInstr
  QX       : ℕ → QCInstr
  QCNOT    : ℕ → ℕ → QCInstr
  QTOFF    : ℕ → ℕ → ℕ → QCInstr
  QMEASURE : ℕ → ℕ → ℕ → QCInstr    -- measure wire i; jump to j/k (basis states)

Wires : Set
Wires = List Bool

flipAt : ℕ → Wires → Wires
flipAt i = updateAt i not

applyCNOT : ℕ → ℕ → Wires → Wires
applyCNOT ctrl tgt ws with lookupDefault false ws ctrl
... | true  = flipAt tgt ws
... | false = ws

applyTOFF : ℕ → ℕ → ℕ → Wires → Wires
applyTOFF c₁ c₂ tgt ws with lookupDefault false ws c₁ | lookupDefault false ws c₂
... | true | true  = flipAt tgt ws
... | true  | false = ws
... | false | true  = ws
... | false | false = ws

record QuantumCircuitCode : Set where
  constructor mkQC
  field
    pc     : ℕ
    outLen : ℕ
    wires  : Wires
    prog   : List QCInstr

open QuantumCircuitCode public

setPCQC : ℕ → QuantumCircuitCode → QuantumCircuitCode
setPCQC n q = mkQC n (outLen q) (wires q) (prog q)

setWiresQC : Wires → QuantumCircuitCode → QuantumCircuitCode
setWiresQC ws q = mkQC (pc q) (outLen q) ws (prog q)

stepQCInstr : QCInstr → QuantumCircuitCode → QuantumCircuitCode
stepQCInstr QCHALT q = q
stepQCInstr QNOP q = setPCQC (suc (pc q)) q
stepQCInstr (QX i) q = setPCQC (suc (pc q)) (setWiresQC (flipAt i (wires q)) q)
stepQCInstr (QCNOT c t) q = setPCQC (suc (pc q)) (setWiresQC (applyCNOT c t (wires q)) q)
stepQCInstr (QTOFF a b t) q = setPCQC (suc (pc q)) (setWiresQC (applyTOFF a b t (wires q)) q)
stepQCInstr (QMEASURE i j k) q with lookupDefault false (wires q) i
... | true  = setPCQC k q
... | false = setPCQC j q

stepQC : QuantumCircuitCode → QuantumCircuitCode
stepQC q = stepQCInstr (lookupDefault QCHALT (prog q) (pc q)) q

-- --------------------------------------------------------------------------
-- Observer-facing interface (deterministic “Born without probabilities”)
--
-- This circuit model is basis-state only: measurement is deterministic and
-- returns the bit already present on a wire. That still supports the CQM shape:
-- “states + effects + measurement”, just without amplitudes.

Effect : Set₁
Effect = Wires → Set

infix 4 _⊨_
_⊨_ : QuantumCircuitCode → Effect → Set
q ⊨ E = E (wires q)

measureWire : ℕ → QuantumCircuitCode → Bool
measureWire i q = lookupDefault false (wires q) i
