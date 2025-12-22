{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.QuantumOracle where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core.Minsky using (Reg; R0; R1; R2; R3)
open import LogOS.Domain.UniversalIR.Core.Utils

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)

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
