{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Core.Minsky where

open import LogOS.Prelude
open import LogOS.UniversalIR.Core.Utils

open import LogOS.Prelude.List using (List; []; _∷_)

-- 1) Minsky machines (4 registers) ------------------------------------------

data Reg : Set where
  R0 R1 R2 R3 : Reg

data MInstr : Set where
  HALT  : MInstr
  INC   : Reg → ℕ → MInstr
  DECJZ : Reg → ℕ → ℕ → MInstr

-- Program/state split (high ROI for staging / partial evaluation stories):
--
-- A *program* is the instruction list; a *state* is the runtime machine state.
-- The combined configuration `MinskyCode` keeps the old user-facing API
-- (`mkM`, `pc`, `r0`, …, `prog`) via a bidirectional pattern synonym.

record MinskyProg : Set where
  constructor mkProg
  field
    prog : List MInstr

record MinskyState : Set where
  constructor mkState
  field
    pc   : ℕ
    r0   : ℕ
    r1   : ℕ
    r2   : ℕ
    r3   : ℕ

record MinskyCode : Set where
  constructor mkCode
  field
    State : MinskyState
    Prog  : MinskyProg

  open MinskyState State public using (pc; r0; r1; r2; r3)
  open MinskyProg Prog public using (prog)

pattern mkM pc r0 r1 r2 r3 prog = mkCode (mkState pc r0 r1 r2 r3) (mkProg prog)

open MinskyCode public using (pc; r0; r1; r2; r3; prog)

getReg : Reg → MinskyCode → ℕ
getReg R0 m = r0 m
getReg R1 m = r1 m
getReg R2 m = r2 m
getReg R3 m = r3 m

setReg : Reg → ℕ → MinskyCode → MinskyCode
setReg R0 n m = mkM (pc m) n       (r1 m) (r2 m) (r3 m) (prog m)
setReg R1 n m = mkM (pc m) (r0 m)  n      (r2 m) (r3 m) (prog m)
setReg R2 n m = mkM (pc m) (r0 m)  (r1 m) n      (r3 m) (prog m)
setReg R3 n m = mkM (pc m) (r0 m)  (r1 m) (r2 m) n      (prog m)

setPC : ℕ → MinskyCode → MinskyCode
setPC n m = mkM n (r0 m) (r1 m) (r2 m) (r3 m) (prog m)

stepM : MinskyCode → MinskyCode
stepM m with lookupDefault HALT (prog m) (pc m)
... | HALT = m
... | INC r j = setPC j (setReg r (suc (getReg r m)) m)
... | DECJZ r j k with getReg r m
... | zero    = setPC k m
... | suc n   = setPC j (setReg r n m)

-- Observer-facing boundary (default: output register r0).

boundaryOutput : BoundaryObs MinskyCode
boundaryOutput = record { Obs = ℕ ; observe = r0 }

Effect : Set₁
Effect = EffectAt boundaryOutput

infix 4 _⊨_
_⊨_ : MinskyCode → Effect → Set
m ⊨ E = (m ⊨ᵇ boundaryOutput) E

-- Fuel helper for the standard DECJZ/INC loop used in the addition demos.
-- For an initial counter value `n`, this is exactly 2·n + 1 steps:
-- one DECJZ to exit, plus (DECJZ; INC) per decrement.

fuelAddR1 : ℕ → ℕ
fuelAddR1 zero    = suc zero
fuelAddR1 (suc n) = suc (suc (fuelAddR1 n))
