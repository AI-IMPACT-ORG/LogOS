{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.Minsky where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core.Utils

open import LogOS.Prelude.List using (List; []; _∷_)

-- 1) Minsky machines (4 registers) ------------------------------------------

data Reg : Set where
  R0 R1 R2 R3 : Reg

data MInstr : Set where
  HALT  : MInstr
  INC   : Reg → ℕ → MInstr
  DECJZ : Reg → ℕ → ℕ → MInstr

record MinskyCode : Set where
  constructor mkM
  field
    pc   : ℕ
    r0   : ℕ
    r1   : ℕ
    r2   : ℕ
    r3   : ℕ
    prog : List MInstr

open MinskyCode public

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
