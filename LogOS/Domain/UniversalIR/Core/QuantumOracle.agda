{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.QuantumOracle where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core.Minsky using (Reg; R0; R1; R2; R3)
open import LogOS.Domain.UniversalIR.Core.Utils

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.Product using (_×_; _,_)

-- 4) Oracle-with-classical-control (oracle tape) -----------------------------

data QInstr : Set where
  QHALT  : QInstr
  QINC   : Reg → ℕ → QInstr
  QDECJZ : Reg → ℕ → ℕ → QInstr
  MEASURE : ℕ → ℕ → ℕ → QInstr     -- consume oracle bit; branch to j/k

record QuantumCode : Set where
  constructor mkQ
  field
    pc     : ℕ
    r0     : ℕ
    r1     : ℕ
    r2     : ℕ
    r3     : ℕ
    oracle : List Bool
    prog   : List QInstr

open QuantumCode public

getRegQ : Reg → QuantumCode → ℕ
getRegQ R0 q = r0 q
getRegQ R1 q = r1 q
getRegQ R2 q = r2 q
getRegQ R3 q = r3 q

setRegQ : Reg → ℕ → QuantumCode → QuantumCode
setRegQ R0 n q = mkQ (pc q) n      (r1 q) (r2 q) (r3 q) (oracle q) (prog q)
setRegQ R1 n q = mkQ (pc q) (r0 q) n      (r2 q) (r3 q) (oracle q) (prog q)
setRegQ R2 n q = mkQ (pc q) (r0 q) (r1 q) n      (r3 q) (oracle q) (prog q)
setRegQ R3 n q = mkQ (pc q) (r0 q) (r1 q) (r2 q) n      (oracle q) (prog q)

setPCQ : ℕ → QuantumCode → QuantumCode
setPCQ n q = mkQ n (r0 q) (r1 q) (r2 q) (r3 q) (oracle q) (prog q)

stepQInstr : QInstr → QuantumCode → QuantumCode
stepQInstr QHALT q = q
stepQInstr (QINC r j) q = setPCQ j (setRegQ r (suc (getRegQ r q)) q)
stepQInstr (QDECJZ r j k) q with getRegQ r q
... | zero  = setPCQ k q
... | suc n = setPCQ j (setRegQ r n q)
stepQInstr (MEASURE _ j k) q with oracle q
... | []          = setPCQ j q
... | true  ∷ bs  = setPCQ k (mkQ (pc q) (r0 q) (r1 q) (r2 q) (r3 q) bs (prog q))
... | false ∷ bs  = setPCQ j (mkQ (pc q) (r0 q) (r1 q) (r2 q) (r3 q) bs (prog q))

stepQ : QuantumCode → QuantumCode
stepQ q = stepQInstr (lookupDefault QHALT (prog q) (pc q)) q

-- --------------------------------------------------------------------------
-- Observer-facing interface (registers only; oracle tape is hidden).
--
-- This makes the observational boundary explicit: `MEASURE` can influence
-- control flow and consume oracle bits, but observers see only the registers.

Regs : Set
Regs = ℕ × ℕ × ℕ × ℕ

observeRegs : QuantumCode → Regs
observeRegs q = (r0 q , r1 q , r2 q , r3 q)

boundaryRegs : BoundaryObs Regs
boundaryRegs = record { Obs = Regs ; observe = λ r → r }

Effect : Set₁
Effect = EffectAt boundaryRegs

infix 4 _⊨_
_⊨_ : QuantumCode → Effect → Set
q ⊨ E = (observeRegs q ⊨ᵇ boundaryRegs) E
