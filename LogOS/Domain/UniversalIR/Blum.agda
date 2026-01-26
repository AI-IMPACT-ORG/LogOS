{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Blum where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ¬_)

open import LogOS.Prelude.Product using (Σ; _,_)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Prelude.Maybe using (just; nothing)

open import LogOS.Computation.Core using (Computation)
open import LogOS.Computation.Blum using (Blum; TimeLeSound; semiDomain)
import LogOS.Computation.SemiDecider as SD

open import LogOS.Domain.UniversalIR.Core

-- Halting predicates ---------------------------------------------------------
-- We deliberately choose *syntactic* halting tests (HALT/STOP/… at the current pc),
-- so `TimeLe n u` is decidable by bounded simulation.

haltMInstr : MInstr → Set
haltMInstr HALT = ⊤
haltMInstr (INC _ _) = ⊥
haltMInstr (DECJZ _ _ _) = ⊥

haltsM : MinskyCode → Set
haltsM m = haltMInstr (lookupDefault HALT (prog m) (pc m))

haltEInstr : EInstr → Set
haltEInstr STOP = ⊤
haltEInstr (PUSH _) = ⊥
haltEInstr POP = ⊥
haltEInstr ADD = ⊥
haltEInstr MUL = ⊥
haltEInstr SUB = ⊥
haltEInstr DUP = ⊥
haltEInstr SWAP = ⊥
haltEInstr JUMP = ⊥
haltEInstr JUMPI = ⊥
haltEInstr MLOAD = ⊥
haltEInstr MSTORE = ⊥

haltsE : EVMCode → Set
haltsE e = haltEInstr (lookupDefault STOP (code e) (EVMCode.pc e))

-- Lambda: halts when there is no β-step available (normal form for this stepper).
haltsL : LambdaCode → Set
haltsL l with stepMaybeL (term l)
... | nothing = ⊤
... | just _  = ⊥

haltQInstr : QInstr → Set
haltQInstr QHALT = ⊤
haltQInstr (QINC _ _) = ⊥
haltQInstr (QDECJZ _ _ _) = ⊥
haltQInstr (MEASURE _ _ _) = ⊥

haltsQ : QuantumCode → Set
haltsQ q = haltQInstr (lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q))

haltQCInstr : QCInstr → Set
haltQCInstr QCHALT = ⊤
haltQCInstr QNOP = ⊥
haltQCInstr (QX _) = ⊥
haltQCInstr (QCNOT _ _) = ⊥
haltQCInstr (QTOFF _ _ _) = ⊥
haltQCInstr (QMEASURE _ _ _) = ⊥

haltsQC : QuantumCircuitCode → Set
haltsQC q = haltQCInstr (lookupDefault QCHALT (QuantumCircuitCode.prog q) (QuantumCircuitCode.pc q))

haltsU : UCode → Set
haltsU (UM m)  = haltsM m
haltsU (UL l)  = haltsL l
haltsU (UE e)  = haltsE e
haltsU (UQ q)  = haltsQ q
haltsU (UQC q) = haltsQC q

decHaltsU : ∀ u → haltsU u ⊎ ¬ haltsU u
decHaltsU (UM m) with lookupDefault HALT (prog m) (pc m)
... | HALT = inj₁ tt
... | INC _ _ = inj₂ (λ ())
... | DECJZ _ _ _ = inj₂ (λ ())
decHaltsU (UE e) with lookupDefault STOP (code e) (EVMCode.pc e)
... | STOP = inj₁ tt
... | PUSH _ = inj₂ (λ ())
... | POP = inj₂ (λ ())
... | ADD = inj₂ (λ ())
... | MUL = inj₂ (λ ())
... | SUB = inj₂ (λ ())
... | DUP = inj₂ (λ ())
... | SWAP = inj₂ (λ ())
... | JUMP = inj₂ (λ ())
... | JUMPI = inj₂ (λ ())
... | MLOAD = inj₂ (λ ())
... | MSTORE = inj₂ (λ ())
decHaltsU (UL l) with stepMaybeL (term l)
... | nothing = inj₁ tt
... | just _  = inj₂ (λ ())
decHaltsU (UQ q) with lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q)
... | QHALT = inj₁ tt
... | QINC _ _ = inj₂ (λ ())
... | QDECJZ _ _ _ = inj₂ (λ ())
... | MEASURE _ _ _ = inj₂ (λ ())
decHaltsU (UQC q) with lookupDefault QCHALT (QuantumCircuitCode.prog q) (QuantumCircuitCode.pc q)
... | QCHALT = inj₁ tt
... | QNOP = inj₂ (λ ())
... | QX _ = inj₂ (λ ())
... | QCNOT _ _ = inj₂ (λ ())
... | QTOFF _ _ _ = inj₂ (λ ())
... | QMEASURE _ _ _ = inj₂ (λ ())

-- Blum structure -------------------------------------------------------------

CompU : Computation UCode
CompU = record { Step = stepU ; Halts = haltsU }

-- “Runs within n steps”: after n small-steps, we are in a syntactic halting state.
TimeLeU : ℕ → UCode → Set
TimeLeU n u = haltsU (simulate n u)

-- Halting domain: codes that halt within some finite number of steps.
DomainU : UCode → Set
DomainU u = Σ ℕ (λ n → TimeLeU n u)

totalU : ∀ u → DomainU u → Σ ℕ (λ n → TimeLeU n u)
totalU _ d = d

decTimeLeU : ∀ n u → TimeLeU n u ⊎ ¬ TimeLeU n u
decTimeLeU zero    u = decHaltsU u
decTimeLeU (suc n) u = decTimeLeU n (stepU u)

BlumU : Blum UCode
BlumU = record
  { Comp   = CompU
  ; TimeLe = TimeLeU
  ; Domain = DomainU
  ; total  = totalU
  ; dec    = decTimeLeU
  }

-- Semidecidability of the unbounded halting domain:
-- `DomainU u` iff some bounded time witness `TimeLeU n u` holds.

soundTimeLeU : TimeLeSound BlumU
soundTimeLeU = record { sound = λ n u t → n , t }

semiDomainU : SD.SemiDecider UCode DomainU
semiDomainU = semiDomain BlumU soundTimeLeU
