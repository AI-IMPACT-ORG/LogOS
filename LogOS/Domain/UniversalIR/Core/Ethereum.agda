{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.Ethereum where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core.Utils

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

-- 3) EVM-like stack machine (unbounded memory, jumps) ------------------------

data EInstr : Set where
  STOP   : EInstr
  PUSH   : ℕ → EInstr
  POP    : EInstr
  ADD    : EInstr
  MUL    : EInstr
  SUB    : EInstr
  DUP    : EInstr
  SWAP   : EInstr
  JUMP   : EInstr
  JUMPI  : EInstr
  MLOAD  : EInstr
  MSTORE : EInstr

Mem : Set
Mem = ℕ → ℕ

mem0 : Mem
mem0 _ = 0

memSet : Mem → ℕ → ℕ → Mem
memSet m k v = λ i → if (i ==ℕ k) then v else m i

record EVMCode : Set where
  constructor mkE
  field
    pc    : ℕ
    stack : List ℕ
    mem   : Mem
    code  : List EInstr

open EVMCode public

push : ℕ → List ℕ → List ℕ
push x xs = x ∷ xs

pop1 : List ℕ → Maybe (ℕ × List ℕ)
pop1 []       = nothing
pop1 (x ∷ xs) = just (x , xs)

pop2 : List ℕ → Maybe (ℕ × ℕ × List ℕ)
pop2 xs with pop1 xs
... | nothing = nothing
... | just (a , xs′) with pop1 xs′
...   | nothing = nothing
...   | just (b , xs″) = just (a , b , xs″)

nonZero : ℕ → Bool
nonZero zero    = false
nonZero (suc _) = true

stepEInstr : EInstr → EVMCode → EVMCode
stepEInstr STOP s = s
stepEInstr (PUSH n) s = mkE (suc (pc s)) (push n (stack s)) (mem s) (code s)
stepEInstr POP s with pop1 (stack s)
... | nothing        = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (_ , xs′) = mkE (suc (pc s)) xs′      (mem s) (code s)
stepEInstr DUP s with pop1 (stack s)
... | nothing        = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (a , xs′) = mkE (suc (pc s)) (a ∷ a ∷ xs′) (mem s) (code s)
stepEInstr SWAP s with pop2 (stack s)
... | nothing            = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (a , b , xs′) = mkE (suc (pc s)) (b ∷ a ∷ xs′) (mem s) (code s)
stepEInstr ADD s with pop2 (stack s)
... | nothing            = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (a , b , xs′) = mkE (suc (pc s)) (push (a + b) xs′) (mem s) (code s)
stepEInstr MUL s with pop2 (stack s)
... | nothing            = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (a , b , xs′) = mkE (suc (pc s)) (push (a * b) xs′) (mem s) (code s)
stepEInstr SUB s with pop2 (stack s)
... | nothing            = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (a , b , xs′) = mkE (suc (pc s)) (push (b ∸ a) xs′) (mem s) (code s)
stepEInstr JUMP s with pop1 (stack s)
... | nothing         = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (dst , xs′) = mkE dst xs′ (mem s) (code s)
stepEInstr JUMPI s with pop2 (stack s)
... | nothing               = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (dst , cnd , xs′) =
    if nonZero cnd
    then mkE dst xs′ (mem s) (code s)
    else mkE (suc (pc s)) xs′ (mem s) (code s)
stepEInstr MLOAD s with pop1 (stack s)
... | nothing           = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (addr , xs′) = mkE (suc (pc s)) (push (mem s addr) xs′) (mem s) (code s)
stepEInstr MSTORE s with pop2 (stack s)
... | nothing                = mkE (suc (pc s)) (stack s) (mem s) (code s)
... | just (addr , val , xs′) =
    mkE (suc (pc s)) xs′ (memSet (mem s) addr val) (code s)

stepE : EVMCode → EVMCode
stepE s = stepEInstr (lookupDefault STOP (code s) (pc s)) s
