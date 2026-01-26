{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Theorems where

open import LogOS.Prelude

open import LogOS.Syntax.Prop using (⊥)
open import LogOS.Prelude.List using (List; []; _∷_; map)
open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.Maybe using (nothing)

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.IR using (lowerToIR; decode; observe; take; bitsToNat; double)
open import LogOS.Domain.UniversalIR.Std
open import LogOS.Domain.UniversalIR.Task
open import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
open import LogOS.Domain.UniversalIR.Languages.Lambda as Lambda
open import LogOS.Domain.UniversalIR.Languages.Ethereum as Ether
open import LogOS.Domain.UniversalIR.Languages.QuantumOracle as Oracle
open import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as Circuit
open import LogOS.Domain.UniversalIR.CQM.QuantumCircuitRel public
open import LogOS.Domain.UniversalIR.Encoding as Enc using (incBits; natToBits; length; take-length; bitsToNat-natToBits)
open import LogOS.Domain.UniversalIR.Universality using (simulateUM; simulateUL; simulateUE; simulateUQ; simulateUQC)
open import LogOS.Domain.UniversalIR.Schemes using
  ( minskyMachineScheme
  ; lambdaMachineScheme
  ; ethereumMachineScheme
  ; oracleMachineScheme
  ; quantumCircuitMachineScheme
  ; minskyScheme
  ; lambdaScheme
  ; ethereumScheme
  ; oracleScheme
  ; quantumCircuitScheme
  ; budget₂
  ; Budget
  ; three·
  ; choiceScheme-cost≤budget₂3n,n
  ; minskyChoice
  ; lambdaChoice
  ; ethereumChoice
  ; oracleChoice
  ; quantumCircuitChoice
  )
import LogOS.Computation.Scheme as Sch
open import LogOS.Computation.Core using (Computation; iterate; iterateStep)
import LogOS.Theorems.Meta.ApplicationKit as AppKit

-- --------------------------------------------------------------------------
-- Shared lemmas are provided by `LogOS.Domain.UniversalIR.Std`.

-- --------------------------------------------------------------------------
-- Non-trivial: correctness of the Minsky multiplication backend.

-- Addition loop (pc = 0..2): add `r1` into `r0`.

addSim :
  ∀ r0 r1 →
  simulate (fuelAddR1 r1) (UM (mkM 0 r0 r1 0 0 Minsky.progAdd))
    ≡ UM (mkM 2 (r0 + r1) 0 0 0 Minsky.progAdd)
addSim r0 zero =
  cong (λ x → UM (mkM 2 x 0 0 0 Minsky.progAdd)) (sym (+-zeroʳ r0))
addSim r0 (suc r1) =
  trans
    (addSim (suc r0) r1)
    (cong (λ x → UM (mkM 2 x 0 0 0 Minsky.progAdd))
          (trans refl (sym (+-sucʳ r0 r1))))

-- Inner loop (pc = 1..3): move `r2` into `r3` while incrementing `r0`.

mulInner :
  ∀ r0 r1 r2 r3 →
  simulate (Minsky.fuelInnerMul r2) (UM (mkM 1 r0 r1 r2 r3 Minsky.progMul))
    ≡ UM (mkM 4 (r0 + r2) r1 0 (r3 + r2) Minsky.progMul)
mulInner r0 r1 zero    r3
  rewrite +-zeroʳ r0 | +-zeroʳ r3
  = refl
mulInner r0 r1 (suc r2) r3 =
  trans
    (mulInner (suc r0) r1 r2 (suc r3))
    (cong₂ (λ x y → UM (mkM 4 x r1 0 y Minsky.progMul))
           (swapSuc r0 r2)
           (swapSuc r3 r2))

-- Restore loop (pc = 4..5): move `r3` into `r2` and jump back to pc = 0.

mulRestore :
  ∀ r0 r1 r2 r3 →
  simulate (Minsky.fuelRestoreMul r3) (UM (mkM 4 r0 r1 r2 r3 Minsky.progMul))
    ≡ UM (mkM 0 r0 r1 (r2 + r3) 0 Minsky.progMul)
mulRestore r0 r1 r2 zero
  rewrite +-zeroʳ r2
  = refl
mulRestore r0 r1 r2 (suc r3) =
  trans
    (mulRestore r0 r1 (suc r2) r3)
    (cong (λ x → UM (mkM 0 r0 r1 x 0 Minsky.progMul))
          (swapSuc r2 r3))

-- One outer iteration (pc = 0): decrement `r1` and add `r2` into `r0`.

mulIter :
  ∀ r0 a b →
  simulate (Minsky.perIterMul b) (UM (mkM 0 r0 (suc a) b 0 Minsky.progMul))
    ≡ UM (mkM 0 (r0 + b) a b 0 Minsky.progMul)
mulIter r0 a b =
  trans
    (simulate-+ (Minsky.fuelInnerMul b) (Minsky.fuelRestoreMul b)
      (UM (mkM 1 r0 a b 0 Minsky.progMul)))
    (trans
      (cong (λ u → simulate (Minsky.fuelRestoreMul b) u) (mulInner r0 a b 0))
      (mulRestore (r0 + b) a 0 b))

-- Full multiplication loop correctness, with an arbitrary accumulator in `r0`.

mulSim :
  ∀ acc a b →
  simulate (Minsky.fuelMul a b) (UM (mkM 0 acc a b 0 Minsky.progMul))
    ≡ UM (mkM 6 (acc + (a * b)) 0 b 0 Minsky.progMul)
mulSim acc zero    b
  rewrite +-zeroʳ acc
  = refl
mulSim acc (suc a) b =
  trans
    (simulate-+ (Minsky.perIterMul b) (Minsky.fuelMul a b)
      (UM (mkM 0 acc (suc a) b 0 Minsky.progMul)))
    (trans
      (cong (λ u → simulate (Minsky.fuelMul a b) u) (mulIter acc a b))
      (trans
        (mulSim (acc + b) a b)
        (cong (λ x → UM (mkM 6 x 0 b 0 Minsky.progMul))
              (+-assoc acc b (a * b)))))

-- As a consequence, `run` computes PA multiplication for all inputs.

minsky-mul-correct : ∀ a b → Minsky.run (mkTask Mul a b) ≡ a * b
minsky-mul-correct a b =
  trans
    (cong (λ u → decode (lowerToIR u)) (mulSim 0 a b))
    (decodeChurch-church (a * b))

minsky-add-correct : ∀ a b → Minsky.run (mkTask Add a b) ≡ a + b
minsky-add-correct a b =
  trans
    (cong (λ u → decode (lowerToIR u)) (addSim a b))
    (decodeChurch-church (a + b))

minsky-correct : (t : PATask) → Minsky.run t ≡ eval t
minsky-correct t with PATask.op t
... | Add = minsky-add-correct (PATask.a t) (PATask.b t)
... | Mul = minsky-mul-correct (PATask.a t) (PATask.b t)

-- --------------------------------------------------------------------------
-- Lambda backend correctness (certified Church output).

stepMaybeL-iterApp
  : ∀ n → stepMaybeL (iterApp n (var 1) (var 0)) ≡ nothing
stepMaybeL-iterApp zero = refl
stepMaybeL-iterApp (suc n)
  rewrite stepMaybeL-iterApp n
  = refl

stepMaybeL-church : ∀ n → stepMaybeL (church n) ≡ nothing
stepMaybeL-church n
  rewrite stepMaybeL-iterApp n
  = refl

stepL-church : ∀ n → stepL (church n) ≡ church n
stepL-church n
  rewrite stepMaybeL-church n
  = refl

stepLC-church : ∀ n → stepLC (mkL (church n)) ≡ mkL (church n)
stepLC-church n = cong mkL (stepL-church n)

iter-stepLC-church
  : ∀ n k → iterateStep stepLC n (mkL (church k)) ≡ mkL (church k)
iter-stepLC-church zero    _ = refl
iter-stepLC-church (suc n) k
  rewrite stepLC-church k
  = iter-stepLC-church n k

simulateUL-church
  : ∀ n k → simulate n (UL (mkL (church k))) ≡ UL (mkL (church k))
simulateUL-church n k =
  trans
    (simulateUL n (mkL (church k)))
    (cong UL (iter-stepLC-church n k))

lambda-correct : (t : PATask) → Lambda.run t ≡ eval t
lambda-correct t =
  let n = Lambda.fuel t in
  let v = eval t in
  trans
    (cong decode (cong lowerToIR (simulateUL-church n v)))
    (decodeChurch-church v)

-- --------------------------------------------------------------------------
-- Ethereum backend correctness (straight-line, but stated explicitly).

ethereum-toIR-add : ∀ a b → Ether.toIR (mkTask Add a b) ≡ UL (mkL (church (a + b)))
ethereum-toIR-add _ _ = refl

ethereum-toIR-mul : ∀ a b → Ether.toIR (mkTask Mul a b) ≡ UL (mkL (church (a * b)))
ethereum-toIR-mul _ _ = refl

ethereum-correct : (t : PATask) → Ether.run t ≡ eval t
ethereum-correct t with PATask.op t
... | Add =
  trans
    (cong decode (ethereum-toIR-add (PATask.a t) (PATask.b t)))
    (decodeChurch-church (PATask.a t + PATask.b t))
... | Mul =
  trans
    (cong decode (ethereum-toIR-mul (PATask.a t) (PATask.b t)))
    (decodeChurch-church (PATask.a t * PATask.b t))

minsky≡ethereum : (t : PATask) → Minsky.run t ≡ Ether.run t
minsky≡ethereum t = trans (minsky-correct t) (sym (ethereum-correct t))

-- Forward declarations (used by the scheme-level correctness lemmas below).

oracle-correct : (t : PATask) → Oracle.run t ≡ eval t
circuit-correct : (t : PATask) → Circuit.run t ≡ eval t

-- ============================================================================
-- Scheme view (machines are schemes)
--
-- These lemmas rebase the paradigm examples on the scheme interface:
-- each machine is a `Scheme` whose observation is the universal `observe`.
-- ============================================================================

iterate≡iter
  : ∀ {ℓ} {A : Set ℓ}
    (C : Computation A) (n : ℕ) (a : A)
  → iterate C n a ≡ iterateStep (Computation.Step C) n a
iterate≡iter C zero    _ = refl
iterate≡iter C (suc n) a = iterate≡iter C n (Computation.Step C a)

minskyMachine≡run : (t : PATask) → Sch.run minskyMachineScheme t ≡ Minsky.run t
minskyMachine≡run t =
  let m = Minsky.compileBrand t in
  let n = Minsky.fuel t in
  let C = Sch.Scheme.Comp minskyMachineScheme in
  trans
    (cong (λ m' → decode (lowerToIR (UM m'))) (iterate≡iter C n m))
    (trans (cong (λ u → decode (lowerToIR u)) (sym (simulateUM n m))) refl)

lambdaMachine≡run : (t : PATask) → Sch.run lambdaMachineScheme t ≡ Lambda.run t
lambdaMachine≡run t =
  let l = Lambda.compileBrand t in
  let n = Lambda.fuel t in
  let C = Sch.Scheme.Comp lambdaMachineScheme in
  trans
    (cong (λ l' → decode (lowerToIR (UL l'))) (iterate≡iter C n l))
    (trans (cong (λ u → decode (lowerToIR u)) (sym (simulateUL n l))) refl)

ethereumMachine≡run : (t : PATask) → Sch.run ethereumMachineScheme t ≡ Ether.run t
ethereumMachine≡run t =
  let e = Ether.compileBrand t in
  let n = Ether.fuel t in
  let C = Sch.Scheme.Comp ethereumMachineScheme in
  trans
    (cong (λ e' → decode (lowerToIR (UE e'))) (iterate≡iter C n e))
    (trans (cong (λ u → decode (lowerToIR u)) (sym (simulateUE n e))) refl)

oracleMachine≡run : (t : PATask) → Sch.run oracleMachineScheme t ≡ Oracle.run t
oracleMachine≡run t =
  let q = Oracle.compileBrand t in
  let n = Oracle.fuel t in
  let C = Sch.Scheme.Comp oracleMachineScheme in
  trans
    (cong (λ q' → decode (lowerToIR (UQ q'))) (iterate≡iter C n q))
    (trans (cong (λ u → decode (lowerToIR u)) (sym (simulateUQ n q))) refl)

circuitMachine≡run : (t : PATask) → Sch.run quantumCircuitMachineScheme t ≡ Circuit.run t
circuitMachine≡run t =
  let q = Circuit.compileBrand t in
  let n = Circuit.fuel t in
  let C = Sch.Scheme.Comp quantumCircuitMachineScheme in
  trans
    (cong (λ q' → decode (lowerToIR (UQC q'))) (iterate≡iter C n q))
    (trans (cong (λ u → decode (lowerToIR u)) (sym (simulateUQC n q))) refl)

minskyMachine-correct : (t : PATask) → Sch.run minskyMachineScheme t ≡ eval t
minskyMachine-correct t = trans (minskyMachine≡run t) (minsky-correct t)

-- --------------------------------------------------------------------------
-- Scheme choices (same universal carrier `UCode`, different compilation+fuel)
--
-- These schemes live over the *same* universal process (`UProcess`) and differ
-- only by “representation choice” (which compiler and schedule/fuel you use).
-- Their semantics is still the same, and the theorems below connect them to
-- the corresponding backend `run` functions.

exec≡simulate
  : ∀ n u
  → iterate (Sch.Scheme.Comp minskyScheme) n u ≡ simulate n u
exec≡simulate zero    _ = refl
exec≡simulate (suc n) u = exec≡simulate n (stepU u)

minskyChoiceScheme≡run : (t : PATask) → Sch.run minskyScheme t ≡ Minsky.run t
minskyChoiceScheme≡run t =
  trans
    (cong observe (exec≡simulate (Minsky.fuel t) (Minsky.compile t)))
    refl

lambdaChoiceScheme≡run : (t : PATask) → Sch.run lambdaScheme t ≡ Lambda.run t
lambdaChoiceScheme≡run t =
  trans
    (cong observe (exec≡simulate (Lambda.fuel t) (Lambda.compile t)))
    refl

ethereumChoiceScheme≡run : (t : PATask) → Sch.run ethereumScheme t ≡ Ether.run t
ethereumChoiceScheme≡run t =
  trans
    (cong observe (exec≡simulate (Ether.fuel t) (Ether.compile t)))
    refl

oracleChoiceScheme≡run : (t : PATask) → Sch.run oracleScheme t ≡ Oracle.run t
oracleChoiceScheme≡run t =
  trans
    (cong observe (exec≡simulate (Oracle.fuel t) (Oracle.compile t)))
    refl

circuitChoiceScheme≡run : (t : PATask) → Sch.run quantumCircuitScheme t ≡ Circuit.run t
circuitChoiceScheme≡run t =
  trans
    (cong observe (exec≡simulate (Circuit.fuel t) (Circuit.compile t)))
    refl

lambdaMachine-correct : (t : PATask) → Sch.run lambdaMachineScheme t ≡ eval t
lambdaMachine-correct t = trans (lambdaMachine≡run t) (lambda-correct t)

ethereumMachine-correct : (t : PATask) → Sch.run ethereumMachineScheme t ≡ eval t
ethereumMachine-correct t = trans (ethereumMachine≡run t) (ethereum-correct t)

-- --------------------------------------------------------------------------
-- Oracle backend correctness (derived from Minsky by erasure).

eraseQInstr : QInstr → MInstr
eraseQInstr QHALT             = HALT
eraseQInstr (QINC r j)        = INC r j
eraseQInstr (QDECJZ r j k)    = DECJZ r j k
eraseQInstr (MEASURE _ _ _)   = HALT

eraseQProg : List QInstr → List MInstr
eraseQProg = map eraseQInstr

eraseQ : QuantumCode → MinskyCode
eraseQ q =
  mkM
    (QuantumCode.pc q)
    (QuantumCode.r0 q)
    (QuantumCode.r1 q)
    (QuantumCode.r2 q)
    (QuantumCode.r3 q)
    (eraseQProg (QuantumCode.prog q))

eraseU : UCode → UCode
eraseU (UQ q) = UM (eraseQ q)
eraseU (UM m) = UM m
eraseU (UL l) = UL l
eraseU (UE e) = UE e
eraseU (UQC q) = UQC q

lowerToIR-eraseU : ∀ u → lowerToIR (eraseU u) ≡ lowerToIR u
lowerToIR-eraseU (UQ _) = refl
lowerToIR-eraseU (UM _) = refl
lowerToIR-eraseU (UL _) = refl
lowerToIR-eraseU (UE _) = refl
lowerToIR-eraseU (UQC _) = refl

NoMeasureQ : QInstr → Set
NoMeasureQ QHALT            = ⊤
NoMeasureQ (QINC _ _)       = ⊤
NoMeasureQ (QDECJZ _ _ _)   = ⊤
NoMeasureQ (MEASURE _ _ _)  = ⊥

AllNoMeasureQ : List QInstr → Set
AllNoMeasureQ = AllPred NoMeasureQ

lookupNoMeasureQ
  : ∀ (xs : List QInstr) (n : ℕ)
  → AllNoMeasureQ xs
  → NoMeasureQ (lookupDefault QHALT xs n)
lookupNoMeasureQ xs n nm = lookupAllPred NoMeasureQ QHALT xs n tt nm

lookupDefault-map
  : ∀ {A B : Set} (f : A → B) (d : A) (xs : List A) (n : ℕ)
  → lookupDefault (f d) (map f xs) n ≡ f (lookupDefault d xs n)
lookupDefault-map _ _ [] _ = refl
lookupDefault-map _ _ (_ ∷ _) zero = refl
lookupDefault-map f d (_ ∷ xs) (suc n) = lookupDefault-map f d xs n

stepMInstr : MInstr → MinskyCode → MinskyCode
stepMInstr HALT m = m
stepMInstr (INC r j) m = setPC j (setReg r (suc (getReg r m)) m)
stepMInstr (DECJZ r j k) m with getReg r m
... | zero  = setPC k m
... | suc n = setPC j (setReg r n m)

stepM′ : MinskyCode → MinskyCode
stepM′ m = stepMInstr (lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m)) m

stepM′≡stepM : ∀ m → stepM′ m ≡ stepM m
stepM′≡stepM m with lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m)
... | HALT = refl
... | INC _ _ = refl
... | DECJZ r _ _ with getReg r m
... | zero  = refl
... | suc _ = refl

erase-stepQInstr
  : ∀ instr q → NoMeasureQ instr
  → eraseQ (stepQInstr instr q) ≡ stepMInstr (eraseQInstr instr) (eraseQ q)
erase-stepQInstr QHALT q _ = refl
erase-stepQInstr (QINC R0 _) q _ = refl
erase-stepQInstr (QINC R1 _) q _ = refl
erase-stepQInstr (QINC R2 _) q _ = refl
erase-stepQInstr (QINC R3 _) q _ = refl
erase-stepQInstr (QDECJZ R0 _ _) (mkQ _ r0 _ _ _ _ _) _ with r0
... | zero  = refl
... | suc _ = refl
erase-stepQInstr (QDECJZ R1 _ _) (mkQ _ _ r1 _ _ _ _) _ with r1
... | zero  = refl
... | suc _ = refl
erase-stepQInstr (QDECJZ R2 _ _) (mkQ _ _ _ r2 _ _ _) _ with r2
... | zero  = refl
... | suc _ = refl
erase-stepQInstr (QDECJZ R3 _ _) (mkQ _ _ _ _ r3 _ _) _ with r3
... | zero  = refl
... | suc _ = refl
erase-stepQInstr (MEASURE _ _ _) _ ()

erase-stepQ
  : (q : QuantumCode)
  → AllNoMeasureQ (QuantumCode.prog q)
  → eraseQ (stepQ q) ≡ stepM (eraseQ q)
erase-stepQ q nm =
  let
    instrQ = lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q)
    nmInstr = lookupNoMeasureQ (QuantumCode.prog q) (QuantumCode.pc q) nm
    m = eraseQ q

    lookup≡
      : lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m) ≡ eraseQInstr instrQ
    lookup≡ = lookupDefault-map eraseQInstr QHALT (QuantumCode.prog q) (QuantumCode.pc q)
  in
  trans
    (erase-stepQInstr instrQ q nmInstr)
    (trans
      (cong (λ instr → stepMInstr instr m) (sym lookup≡))
      (stepM′≡stepM m))

prog-stepQInstr : ∀ instr q → QuantumCode.prog (stepQInstr instr q) ≡ QuantumCode.prog q
prog-stepQInstr QHALT _ = refl
prog-stepQInstr (QINC R0 _) _ = refl
prog-stepQInstr (QINC R1 _) _ = refl
prog-stepQInstr (QINC R2 _) _ = refl
prog-stepQInstr (QINC R3 _) _ = refl
prog-stepQInstr (QDECJZ R0 _ _) (mkQ _ r0 _ _ _ _ prog) with r0
... | zero  = refl
... | suc _ = refl
prog-stepQInstr (QDECJZ R1 _ _) (mkQ _ _ r1 _ _ _ prog) with r1
... | zero  = refl
... | suc _ = refl
prog-stepQInstr (QDECJZ R2 _ _) (mkQ _ _ _ r2 _ _ prog) with r2
... | zero  = refl
... | suc _ = refl
prog-stepQInstr (QDECJZ R3 _ _) (mkQ _ _ _ _ r3 _ prog) with r3
... | zero  = refl
... | suc _ = refl
prog-stepQInstr (MEASURE _ _ _) (mkQ _ _ _ _ _ oracle prog) with oracle
... | []         = refl
... | true  ∷ _  = refl
... | false ∷ _  = refl

prog-stepQ : ∀ q → QuantumCode.prog (stepQ q) ≡ QuantumCode.prog q
prog-stepQ q =
  prog-stepQInstr (lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q)) q

AllNoMeasureQ-stepQ
  : ∀ q → AllNoMeasureQ (QuantumCode.prog q) → AllNoMeasureQ (QuantumCode.prog (stepQ q))
AllNoMeasureQ-stepQ q nm rewrite prog-stepQ q = nm

eraseU-stepQ
  : ∀ q → AllNoMeasureQ (QuantumCode.prog q)
  → eraseU (stepU (UQ q)) ≡ stepU (eraseU (UQ q))
eraseU-stepQ q nm = cong UM (erase-stepQ q nm)

eraseU-simulateQ
  : ∀ n q → AllNoMeasureQ (QuantumCode.prog q)
  → eraseU (simulate n (UQ q)) ≡ simulate n (eraseU (UQ q))
eraseU-simulateQ zero q _ = refl
eraseU-simulateQ (suc n) q nm =
  trans
    (eraseU-simulateQ n (stepQ q) (AllNoMeasureQ-stepQ q nm))
    (cong (simulate n) (eraseU-stepQ q nm))

allNoMeasureQ-progAdd : AllNoMeasureQ Oracle.progAdd
allNoMeasureQ-progAdd = tt , (tt , (tt , tt))

allNoMeasureQ-progMul : AllNoMeasureQ Oracle.progMul
allNoMeasureQ-progMul =
  tt , (tt , (tt , (tt , (tt , (tt , (tt , tt))))))

allNoMeasureQ-compileBrand : ∀ t → AllNoMeasureQ (QuantumCode.prog (Oracle.compileBrand t))
allNoMeasureQ-compileBrand t with PATask.op t
... | Add = allNoMeasureQ-progAdd
... | Mul = allNoMeasureQ-progMul

erase-compileBrand : ∀ t → eraseQ (Oracle.compileBrand t) ≡ Minsky.compileBrand t
erase-compileBrand t with PATask.op t
... | Add = refl
... | Mul = refl

fuelInnerMul≡ : ∀ b → Oracle.fuelInnerMul b ≡ Minsky.fuelInnerMul b
fuelInnerMul≡ zero    = refl
fuelInnerMul≡ (suc b) = cong (λ x → suc (suc (suc x))) (fuelInnerMul≡ b)

fuelRestoreMul≡ : ∀ b → Oracle.fuelRestoreMul b ≡ Minsky.fuelRestoreMul b
fuelRestoreMul≡ zero    = refl
fuelRestoreMul≡ (suc b) = cong (λ x → suc (suc x)) (fuelRestoreMul≡ b)

perIterMul≡ : ∀ b → Oracle.perIterMul b ≡ Minsky.perIterMul b
perIterMul≡ b =
  cong suc (cong₂ _+_ (fuelInnerMul≡ b) (fuelRestoreMul≡ b))

fuelMul≡ : ∀ a b → Oracle.fuelMul a b ≡ Minsky.fuelMul a b
fuelMul≡ zero    _ = refl
fuelMul≡ (suc a) b = cong₂ _+_ (perIterMul≡ b) (fuelMul≡ a b)

fuel≡ : ∀ t → Oracle.fuel t ≡ Minsky.fuel t
fuel≡ t with PATask.op t
... | Add = refl
... | Mul = fuelMul≡ (PATask.a t) (PATask.b t)

oracle≡minsky : (t : PATask) → Oracle.run t ≡ Minsky.run t
oracle≡minsky t =
  let
    n  = Oracle.fuel t
    q  = Oracle.compileBrand t
    nm = allNoMeasureQ-compileBrand t

    step₁
      : decode (lowerToIR (simulate n (UQ q)))
        ≡ decode (lowerToIR (eraseU (simulate n (UQ q))))
    step₁ = cong decode (sym (lowerToIR-eraseU (simulate n (UQ q))))

    step₂
      : decode (lowerToIR (eraseU (simulate n (UQ q))))
        ≡ decode (lowerToIR (simulate n (eraseU (UQ q))))
    step₂ = cong decode (cong lowerToIR (eraseU-simulateQ n q nm))

    step₃
      : decode (lowerToIR (simulate n (eraseU (UQ q))))
        ≡ decode (lowerToIR (simulate n (UM (Minsky.compileBrand t))))
    step₃ =
      cong decode
        (cong lowerToIR
          (cong (simulate n)
            (cong UM (erase-compileBrand t))))

    step₄
      : decode (lowerToIR (simulate n (UM (Minsky.compileBrand t))))
        ≡ decode (lowerToIR (simulate (Minsky.fuel t) (UM (Minsky.compileBrand t))))
    step₄ =
      cong
        (λ k → decode (lowerToIR (simulate k (UM (Minsky.compileBrand t)))))
        (fuel≡ t)
  in
  trans step₁ (trans step₂ (trans step₃ step₄))

oracle-correct t = trans (oracle≡minsky t) (minsky-correct t)

-- --------------------------------------------------------------------------
-- Basis-state circuit backend correctness (constant-output compiler).

circuit-correct t =
  let
    ws = Enc.natToBits (eval t)
    n  = bitsToNat (take (Enc.length ws) ws)
  in
  trans
    (decodeChurch-church n)
    (trans
      (cong bitsToNat (take-length ws))
      (bitsToNat-natToBits (eval t)))

-- --------------------------------------------------------------------------
-- Scheme-backend correctness (derived from run≡ + backend correctness).

oracleMachine-correct : (t : PATask) → Sch.run oracleMachineScheme t ≡ eval t
oracleMachine-correct t = trans (oracleMachine≡run t) (oracle-correct t)

circuitMachine-correct : (t : PATask) → Sch.run quantumCircuitMachineScheme t ≡ eval t
circuitMachine-correct t = trans (circuitMachine≡run t) (circuit-correct t)

-- --------------------------------------------------------------------------
-- Choice-scheme correctness (Universal carrier `UCode`)
--
-- These schemes share the same universal process (`UProcess`) and differ only
-- by representation choice (compiler + schedule/fuel).

fuelBudgetFor
  : (S : Sch.Scheme {ℓI = lzero} {ℓO = lzero} {ℓC = lzero} {ℓQ = lzero} PATask ℕ)
  → PATask → Budget
fuelBudgetFor S t = budget₂ (three· (Sch.Scheme.fuel S t)) (Sch.Scheme.fuel S t)

record ChoiceSchemesCorrect (t : PATask) : Set where
  field
    minsky   : Sch.run minskyScheme t ≡ eval t
    lambda   : Sch.run lambdaScheme t ≡ eval t
    ethereum : Sch.run ethereumScheme t ≡ eval t
    oracle   : Sch.run oracleScheme t ≡ eval t
    circuit  : Sch.run quantumCircuitScheme t ≡ eval t

record ChoiceSchemesCostBound (t : PATask) : Set where
  field
    minsky   : Sch.Scheme._≤s_ minskyScheme (Sch.cost minskyScheme t) (fuelBudgetFor minskyScheme t)
    lambda   : Sch.Scheme._≤s_ lambdaScheme (Sch.cost lambdaScheme t) (fuelBudgetFor lambdaScheme t)
    ethereum : Sch.Scheme._≤s_ ethereumScheme (Sch.cost ethereumScheme t) (fuelBudgetFor ethereumScheme t)
    oracle   : Sch.Scheme._≤s_ oracleScheme (Sch.cost oracleScheme t) (fuelBudgetFor oracleScheme t)
    circuit  : Sch.Scheme._≤s_ quantumCircuitScheme (Sch.cost quantumCircuitScheme t) (fuelBudgetFor quantumCircuitScheme t)

record ChoiceSchemesRunEq : Set where
  field
    minsky≈lambda   : Sch.RunEq minskyScheme lambdaScheme
    lambda≈ethereum : Sch.RunEq lambdaScheme ethereumScheme
    ethereum≈oracle : Sch.RunEq ethereumScheme oracleScheme
    oracle≈circuit  : Sch.RunEq oracleScheme quantumCircuitScheme

patask-choiceSchemes-correct : ∀ t → ChoiceSchemesCorrect t
patask-choiceSchemes-correct t =
  record
    { minsky   = trans (minskyChoiceScheme≡run t) (minsky-correct t)
    ; lambda   = trans (lambdaChoiceScheme≡run t) (lambda-correct t)
    ; ethereum = trans (ethereumChoiceScheme≡run t) (ethereum-correct t)
    ; oracle   = trans (oracleChoiceScheme≡run t) (oracle-correct t)
    ; circuit  = trans (circuitChoiceScheme≡run t) (circuit-correct t)
    }

-- --------------------------------------------------------------------------
-- Fuel reaches a fixed point (FuelHalts) and budget-existence corollaries.
--
-- This is where the “fuel-free” (`ComputesTo`) story becomes concrete for the
-- UniversalIR schemes: the chosen fuel schedule really reaches a fixed point of
-- the small-step dynamics, so:
--   - `run` is sound w.r.t. `ComputesTo` (and `ComputesTo` collapses to `run`),
--   - and “unbudgeted = ∃ budgeted” gives an explicit `ComputesWithin` witness.

UM-injective : ∀ {m m'} → UM m ≡ UM m' → m ≡ m'
UM-injective refl = refl

-- Minsky choice scheme: halts because the compiled programs end in `HALT`.
minskyScheme-fuelHalts : Sch.FuelHalts minskyScheme
minskyScheme-fuelHalts (mkTask Add a b) =
  trans
    (cong stepU (exec≡simulate (Sch.fuel minskyScheme (mkTask Add a b)) (Minsky.compile (mkTask Add a b))))
    (trans
      (trans
        (cong stepU (addSim a b))
        (trans refl (sym (addSim a b))))
      (sym (exec≡simulate (Sch.fuel minskyScheme (mkTask Add a b)) (Minsky.compile (mkTask Add a b)))))
minskyScheme-fuelHalts (mkTask Mul a b) =
  trans
    (cong stepU (exec≡simulate (Sch.fuel minskyScheme (mkTask Mul a b)) (Minsky.compile (mkTask Mul a b))))
    (trans
      (trans
        (cong stepU (mulSim 0 a b))
        (trans refl (sym (mulSim 0 a b))))
      (sym (exec≡simulate (Sch.fuel minskyScheme (mkTask Mul a b)) (Minsky.compile (mkTask Mul a b)))))

-- Lambda choice scheme: the compiler emits a Church numeral in normal form.
lambdaScheme-fuelHalts : Sch.FuelHalts lambdaScheme
lambdaScheme-fuelHalts t
  = trans
      (cong stepU (exec≡simulate (Sch.fuel lambdaScheme t) (Lambda.compile t)))
      (trans
        (trans
          (cong stepU (simulateUL-church (Sch.fuel lambdaScheme t) (eval t)))
          (trans
            (cong UL (stepLC-church (eval t)))
            (sym (simulateUL-church (Sch.fuel lambdaScheme t) (eval t)))))
        (sym (exec≡simulate (Sch.fuel lambdaScheme t) (Lambda.compile t))))

-- Ethereum choice scheme: straight-line programs reach the `STOP` instruction.
ethereumScheme-fuelHalts : Sch.FuelHalts ethereumScheme
ethereumScheme-fuelHalts t with PATask.op t
... | Add
  rewrite exec≡simulate (Sch.fuel ethereumScheme t) (Ether.compile t)
  = refl
... | Mul
  rewrite exec≡simulate (Sch.fuel ethereumScheme t) (Ether.compile t)
  = refl

-- Circuit choice scheme: fuel = 0 and the compiled code starts at `QCHALT`.
quantumCircuitScheme-fuelHalts : Sch.FuelHalts quantumCircuitScheme
quantumCircuitScheme-fuelHalts t
  rewrite exec≡simulate (Sch.fuel quantumCircuitScheme t) (Circuit.compile t)
  = refl

-- Oracle choice scheme: derived by erasure to the Minsky halting proof,
-- using the “no measurement” invariant of the compiled programs.

NoMeasureQ-eraseHALT→QHALT
  : ∀ instr → NoMeasureQ instr → eraseQInstr instr ≡ HALT → instr ≡ QHALT
NoMeasureQ-eraseHALT→QHALT QHALT _ _ = refl
NoMeasureQ-eraseHALT→QHALT (QINC _ _) _ ()
NoMeasureQ-eraseHALT→QHALT (QDECJZ _ _ _) _ ()
NoMeasureQ-eraseHALT→QHALT (MEASURE _ _ _) () _

AllNoMeasureQ-iterStepQ
  : ∀ n q → AllNoMeasureQ (QuantumCode.prog q) → AllNoMeasureQ (QuantumCode.prog (iterateStep stepQ n q))
AllNoMeasureQ-iterStepQ zero    q nm = nm
AllNoMeasureQ-iterStepQ (suc n) q nm =
  AllNoMeasureQ-iterStepQ n (stepQ q) (AllNoMeasureQ-stepQ q nm)

oracleHaltsAtFuel
  : ∀ t → stepU (simulate (Oracle.fuel t) (Oracle.compile t)) ≡ simulate (Oracle.fuel t) (Oracle.compile t)
oracleHaltsAtFuel (mkTask Add a b) =
  let
    t  = mkTask Add a b
    n  = Oracle.fuel t
    q0 = Oracle.compileBrand t
    qn = iterateStep stepQ n q0

    nm0 : AllNoMeasureQ (QuantumCode.prog q0)
    nm0 = allNoMeasureQ-compileBrand t

    nmn : AllNoMeasureQ (QuantumCode.prog qn)
    nmn = AllNoMeasureQ-iterStepQ n q0 nm0

    instrQ : QInstr
    instrQ = lookupDefault QHALT (QuantumCode.prog qn) (QuantumCode.pc qn)

    nmInstr : NoMeasureQ instrQ
    nmInstr = lookupNoMeasureQ (QuantumCode.prog qn) (QuantumCode.pc qn) nmn

    -- Erasing the quantum run yields the corresponding Minsky run, which ends in HALT.
    eraseSim≡HALT
      : eraseU (simulate n (UQ q0)) ≡ UM (mkM 2 (a + b) 0 0 0 Minsky.progAdd)
    eraseSim≡HALT =
      trans
        (eraseU-simulateQ n q0 nm0)
        (trans
          (cong (λ u → simulate n u) (cong UM (erase-compileBrand t)))
          (trans
            (cong (λ k → simulate k (UM (Minsky.compileBrand t))) (fuel≡ t))
            (addSim a b)))

    eraseQn≡HALT : eraseQ qn ≡ mkM 2 (a + b) 0 0 0 Minsky.progAdd
    eraseQn≡HALT =
      UM-injective
        (trans
          (sym (cong eraseU (simulateUQ n q0)))
          eraseSim≡HALT)

    -- The looked-up instruction erases to HALT, hence is QHALT (since no MEASURE occurs).
    instrErasesToHALT : eraseQInstr instrQ ≡ HALT
    instrErasesToHALT =
      trans
        (sym (lookupDefault-map eraseQInstr QHALT (QuantumCode.prog qn) (QuantumCode.pc qn)))
        (cong
          (λ m → lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m))
          eraseQn≡HALT)

    instr≡QHALT : instrQ ≡ QHALT
    instr≡QHALT = NoMeasureQ-eraseHALT→QHALT instrQ nmInstr instrErasesToHALT

    stepQn≡ : stepQ qn ≡ qn
    stepQn≡ =
      subst (λ i → stepQInstr i qn ≡ qn) (sym instr≡QHALT) refl
  in
  -- Reduce to the quantum code fixed-point statement.
  trans
    (cong stepU (simulateUQ n q0))
    (trans
      (cong UQ stepQn≡)
      (sym (simulateUQ n q0)))
oracleHaltsAtFuel (mkTask Mul a b) =
  let
    t  = mkTask Mul a b
    n  = Oracle.fuel t
    q0 = Oracle.compileBrand t
    qn = iterateStep stepQ n q0

    nm0 : AllNoMeasureQ (QuantumCode.prog q0)
    nm0 = allNoMeasureQ-compileBrand t

    nmn : AllNoMeasureQ (QuantumCode.prog qn)
    nmn = AllNoMeasureQ-iterStepQ n q0 nm0

    instrQ : QInstr
    instrQ = lookupDefault QHALT (QuantumCode.prog qn) (QuantumCode.pc qn)

    nmInstr : NoMeasureQ instrQ
    nmInstr = lookupNoMeasureQ (QuantumCode.prog qn) (QuantumCode.pc qn) nmn

    eraseSim≡HALT
      : eraseU (simulate n (UQ q0)) ≡ UM (mkM 6 (0 + (a * b)) 0 b 0 Minsky.progMul)
    eraseSim≡HALT =
      trans
        (eraseU-simulateQ n q0 nm0)
        (trans
          (cong (λ u → simulate n u) (cong UM (erase-compileBrand t)))
          (trans
            (cong (λ k → simulate k (UM (Minsky.compileBrand t))) (fuel≡ t))
            (mulSim 0 a b)))

    eraseQn≡HALT : eraseQ qn ≡ mkM 6 (0 + (a * b)) 0 b 0 Minsky.progMul
    eraseQn≡HALT =
      UM-injective
        (trans
          (sym (cong eraseU (simulateUQ n q0)))
          eraseSim≡HALT)

    instrErasesToHALT : eraseQInstr instrQ ≡ HALT
    instrErasesToHALT =
      trans
        (sym (lookupDefault-map eraseQInstr QHALT (QuantumCode.prog qn) (QuantumCode.pc qn)))
        (cong
          (λ m → lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m))
          eraseQn≡HALT)

    instr≡QHALT : instrQ ≡ QHALT
    instr≡QHALT = NoMeasureQ-eraseHALT→QHALT instrQ nmInstr instrErasesToHALT

    stepQn≡ : stepQ qn ≡ qn
    stepQn≡ =
      subst (λ i → stepQInstr i qn ≡ qn) (sym instr≡QHALT) refl
  in
  trans
    (cong stepU (simulateUQ n q0))
    (trans
      (cong UQ stepQn≡)
      (sym (simulateUQ n q0)))

oracleScheme-fuelHalts : Sch.FuelHalts oracleScheme
oracleScheme-fuelHalts t
  = trans
      (cong stepU (exec≡simulate (Sch.fuel oracleScheme t) (Oracle.compile t)))
      (trans
        (oracleHaltsAtFuel t)
        (sym (exec≡simulate (Sch.fuel oracleScheme t) (Oracle.compile t))))

-- Corollaries: fuel schedule soundness and “∃ budget” witnesses.

module FS-minsky = Sch.FuelSound minskyScheme
module FS-lambda = Sch.FuelSound lambdaScheme
module FS-ethereum = Sch.FuelSound ethereumScheme
module FS-oracle = Sch.FuelSound oracleScheme
module FS-circuit = Sch.FuelSound quantumCircuitScheme

minskyScheme-runComputesTo : ∀ t → Sch.ComputesTo minskyScheme t (Sch.run minskyScheme t)
minskyScheme-runComputesTo t = FS-minsky.runIsComputesTo minskyScheme-fuelHalts t

lambdaScheme-runComputesTo : ∀ t → Sch.ComputesTo lambdaScheme t (Sch.run lambdaScheme t)
lambdaScheme-runComputesTo t = FS-lambda.runIsComputesTo lambdaScheme-fuelHalts t

ethereumScheme-runComputesTo : ∀ t → Sch.ComputesTo ethereumScheme t (Sch.run ethereumScheme t)
ethereumScheme-runComputesTo t = FS-ethereum.runIsComputesTo ethereumScheme-fuelHalts t

oracleScheme-runComputesTo : ∀ t → Sch.ComputesTo oracleScheme t (Sch.run oracleScheme t)
oracleScheme-runComputesTo t = FS-oracle.runIsComputesTo oracleScheme-fuelHalts t

quantumCircuitScheme-runComputesTo : ∀ t → Sch.ComputesTo quantumCircuitScheme t (Sch.run quantumCircuitScheme t)
quantumCircuitScheme-runComputesTo t = FS-circuit.runIsComputesTo quantumCircuitScheme-fuelHalts t

minskyScheme-runComputesWithinSomeBudget
  : ∀ t → Σ Budget (λ b → Sch.ComputesWithin minskyScheme t b (Sch.run minskyScheme t))
minskyScheme-runComputesWithinSomeBudget t =
  Sch.ComputesTo→∃ComputesWithin minskyScheme (minskyScheme-runComputesTo t)

lambdaScheme-runComputesWithinSomeBudget
  : ∀ t → Σ Budget (λ b → Sch.ComputesWithin lambdaScheme t b (Sch.run lambdaScheme t))
lambdaScheme-runComputesWithinSomeBudget t =
  Sch.ComputesTo→∃ComputesWithin lambdaScheme {x = t} {y = Sch.run lambdaScheme t}
    (lambdaScheme-runComputesTo t)

ethereumScheme-runComputesWithinSomeBudget
  : ∀ t → Σ Budget (λ b → Sch.ComputesWithin ethereumScheme t b (Sch.run ethereumScheme t))
ethereumScheme-runComputesWithinSomeBudget t =
  Sch.ComputesTo→∃ComputesWithin ethereumScheme (ethereumScheme-runComputesTo t)

oracleScheme-runComputesWithinSomeBudget
  : ∀ t → Σ Budget (λ b → Sch.ComputesWithin oracleScheme t b (Sch.run oracleScheme t))
oracleScheme-runComputesWithinSomeBudget t =
  Sch.ComputesTo→∃ComputesWithin oracleScheme (oracleScheme-runComputesTo t)

quantumCircuitScheme-runComputesWithinSomeBudget
  : ∀ t → Σ Budget (λ b → Sch.ComputesWithin quantumCircuitScheme t b (Sch.run quantumCircuitScheme t))
quantumCircuitScheme-runComputesWithinSomeBudget t =
  Sch.ComputesTo→∃ComputesWithin quantumCircuitScheme {x = t} {y = Sch.run quantumCircuitScheme t}
    (quantumCircuitScheme-runComputesTo t)

patask-choiceSchemes-costBound : ∀ t → ChoiceSchemesCostBound t
patask-choiceSchemes-costBound t =
  record
    { minsky   = choiceScheme-cost≤budget₂3n,n minskyChoice t
    ; lambda   = choiceScheme-cost≤budget₂3n,n lambdaChoice t
    ; ethereum = choiceScheme-cost≤budget₂3n,n ethereumChoice t
    ; oracle   = choiceScheme-cost≤budget₂3n,n oracleChoice t
    ; circuit  = choiceScheme-cost≤budget₂3n,n quantumCircuitChoice t
    }

-- Cost honesty yields explicit budgeted computation witnesses for `run`.

minskyScheme-runComputesWithinFuelBudgetFor
  : ∀ t → Sch.ComputesWithin minskyScheme t (fuelBudgetFor minskyScheme t) (Sch.run minskyScheme t)
minskyScheme-runComputesWithinFuelBudgetFor t =
  FS-minsky.runIsComputesWithin minskyScheme-fuelHalts t (fuelBudgetFor minskyScheme t)
    (ChoiceSchemesCostBound.minsky (patask-choiceSchemes-costBound t))

lambdaScheme-runComputesWithinFuelBudgetFor
  : ∀ t → Sch.ComputesWithin lambdaScheme t (fuelBudgetFor lambdaScheme t) (Sch.run lambdaScheme t)
lambdaScheme-runComputesWithinFuelBudgetFor t =
  FS-lambda.runIsComputesWithin lambdaScheme-fuelHalts t (fuelBudgetFor lambdaScheme t)
    (ChoiceSchemesCostBound.lambda (patask-choiceSchemes-costBound t))

ethereumScheme-runComputesWithinFuelBudgetFor
  : ∀ t → Sch.ComputesWithin ethereumScheme t (fuelBudgetFor ethereumScheme t) (Sch.run ethereumScheme t)
ethereumScheme-runComputesWithinFuelBudgetFor t =
  FS-ethereum.runIsComputesWithin ethereumScheme-fuelHalts t (fuelBudgetFor ethereumScheme t)
    (ChoiceSchemesCostBound.ethereum (patask-choiceSchemes-costBound t))

oracleScheme-runComputesWithinFuelBudgetFor
  : ∀ t → Sch.ComputesWithin oracleScheme t (fuelBudgetFor oracleScheme t) (Sch.run oracleScheme t)
oracleScheme-runComputesWithinFuelBudgetFor t =
  FS-oracle.runIsComputesWithin oracleScheme-fuelHalts t (fuelBudgetFor oracleScheme t)
    (ChoiceSchemesCostBound.oracle (patask-choiceSchemes-costBound t))

quantumCircuitScheme-runComputesWithinFuelBudgetFor
  : ∀ t → Sch.ComputesWithin quantumCircuitScheme t (fuelBudgetFor quantumCircuitScheme t) (Sch.run quantumCircuitScheme t)
quantumCircuitScheme-runComputesWithinFuelBudgetFor t =
  FS-circuit.runIsComputesWithin quantumCircuitScheme-fuelHalts t (fuelBudgetFor quantumCircuitScheme t)
    (ChoiceSchemesCostBound.circuit (patask-choiceSchemes-costBound t))

patask-choiceSchemes-runEq : ChoiceSchemesRunEq
patask-choiceSchemes-runEq =
  record
    { minsky≈lambda = λ t →
        let c = patask-choiceSchemes-correct t in
        trans (ChoiceSchemesCorrect.minsky c)
              (sym (ChoiceSchemesCorrect.lambda c))
    ; lambda≈ethereum = λ t →
        let c = patask-choiceSchemes-correct t in
        trans (ChoiceSchemesCorrect.lambda c)
              (sym (ChoiceSchemesCorrect.ethereum c))
    ; ethereum≈oracle = λ t →
        let c = patask-choiceSchemes-correct t in
        trans (ChoiceSchemesCorrect.ethereum c)
              (sym (ChoiceSchemesCorrect.oracle c))
    ; oracle≈circuit = λ t →
        let c = patask-choiceSchemes-correct t in
        trans (ChoiceSchemesCorrect.oracle c)
              (sym (ChoiceSchemesCorrect.circuit c))
    }

-- --------------------------------------------------------------------------
-- Algorithms vs implementations (first-class separation)
--
-- An algorithm is a machine-independent specification. A scheme is one
-- implementation choice. Here: the PA task evaluator `eval` is specified as the
-- unique correct output; each scheme provides an implementation.

PAAlg : Sch.Algorithm PATask ℕ
PAAlg = record { Spec = λ t n → n ≡ eval t }

minsky-implements-PA : Sch.ImplementsRun PAAlg minskyScheme
minsky-implements-PA = record { correct = λ t → ChoiceSchemesCorrect.minsky (patask-choiceSchemes-correct t) }

lambda-implements-PA : Sch.ImplementsRun PAAlg lambdaScheme
lambda-implements-PA = record { correct = λ t → ChoiceSchemesCorrect.lambda (patask-choiceSchemes-correct t) }

ethereum-implements-PA : Sch.ImplementsRun PAAlg ethereumScheme
ethereum-implements-PA = record { correct = λ t → ChoiceSchemesCorrect.ethereum (patask-choiceSchemes-correct t) }

oracle-implements-PA : Sch.ImplementsRun PAAlg oracleScheme
oracle-implements-PA = record { correct = λ t → ChoiceSchemesCorrect.oracle (patask-choiceSchemes-correct t) }

circuit-implements-PA : Sch.ImplementsRun PAAlg quantumCircuitScheme
circuit-implements-PA = record { correct = λ t → ChoiceSchemesCorrect.circuit (patask-choiceSchemes-correct t) }

-- Relational correctness: any computed outcome satisfies the algorithm spec.
--
-- This is the “fuel-free” semantics surface: a scheme’s chosen fuel schedule is
-- only one way to reach a stable output. Under `FuelHalts`, all executions agree
-- with `run`, so schedule-correctness upgrades to relational correctness.

minsky-implementsRel-PA : Sch.ImplementsRel PAAlg minskyScheme
minsky-implementsRel-PA =
  Sch.run→rel minskyScheme-fuelHalts minsky-implements-PA

lambda-implementsRel-PA : Sch.ImplementsRel PAAlg lambdaScheme
lambda-implementsRel-PA =
  Sch.run→rel lambdaScheme-fuelHalts lambda-implements-PA

ethereum-implementsRel-PA : Sch.ImplementsRel PAAlg ethereumScheme
ethereum-implementsRel-PA =
  Sch.run→rel ethereumScheme-fuelHalts ethereum-implements-PA

oracle-implementsRel-PA : Sch.ImplementsRel PAAlg oracleScheme
oracle-implementsRel-PA =
  Sch.run→rel oracleScheme-fuelHalts oracle-implements-PA

circuit-implementsRel-PA : Sch.ImplementsRel PAAlg quantumCircuitScheme
circuit-implementsRel-PA =
  Sch.run→rel quantumCircuitScheme-fuelHalts circuit-implements-PA

-- ============================================================================
-- One theorem: “same computation, many representations” (PA fragment)
--
-- This is the single aggregation point for the publication story:
-- Minsky / λ-calculus / EVM-like / oracle-with-control / explicit circuits all
-- compute the same `PATask` meaning, and agreement can be stated in one line.
-- ============================================================================

infix 4 _≈Scheme_

_≈Scheme_
  : ∀ {ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
  → Sch.Scheme {ℓI = lzero} {ℓO = lzero} {ℓC = ℓC₁} {ℓQ = ℓQ₁} PATask ℕ
  → Sch.Scheme {ℓI = lzero} {ℓO = lzero} {ℓC = ℓC₂} {ℓQ = ℓQ₂} PATask ℕ
  → Set
S ≈Scheme T = ∀ t → Sch.run S t ≡ Sch.run T t

-- Same statement, but using the generic scheme equivalence alias.
--
-- This is the recommended interface for downstream “machines as schemes”
-- packaging: it matches the standard compiler-correctness “same function”
-- notion and composes by `Sch.RunEq-trans`.

infix 4 _≈RunEq_

_≈RunEq_
  : ∀ {ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
  → Sch.Scheme {ℓI = lzero} {ℓO = lzero} {ℓC = ℓC₁} {ℓQ = ℓQ₁} PATask ℕ
  → Sch.Scheme {ℓI = lzero} {ℓO = lzero} {ℓC = ℓC₂} {ℓQ = ℓQ₂} PATask ℕ
  → Set
S ≈RunEq T = Sch.RunEq S T

record ParadigmsCorrect (t : PATask) : Set where
  field
    minsky   : Sch.run minskyMachineScheme t ≡ eval t
    lambda   : Sch.run lambdaMachineScheme t ≡ eval t
    ethereum : Sch.run ethereumMachineScheme t ≡ eval t
    oracle   : Sch.run oracleMachineScheme t ≡ eval t
    circuit  : Sch.run quantumCircuitMachineScheme t ≡ eval t

record ParadigmsRunEq : Set where
  field
    minsky≈lambda   : _≈RunEq_ minskyMachineScheme lambdaMachineScheme
    lambda≈ethereum : _≈RunEq_ lambdaMachineScheme ethereumMachineScheme
    ethereum≈oracle : _≈RunEq_ ethereumMachineScheme oracleMachineScheme
    oracle≈circuit  : _≈RunEq_ oracleMachineScheme quantumCircuitMachineScheme

patask-paradigms-correct : ∀ t → ParadigmsCorrect t
patask-paradigms-correct t =
  record
    { minsky   = minskyMachine-correct t
    ; lambda   = lambdaMachine-correct t
    ; ethereum = ethereumMachine-correct t
    ; oracle   = oracleMachine-correct t
    ; circuit  = circuitMachine-correct t
    }

patask-paradigms-runEq : ParadigmsRunEq
patask-paradigms-runEq =
  record
    { minsky≈lambda = λ t →
        let c = patask-paradigms-correct t in
        trans (ParadigmsCorrect.minsky c)
              (sym (ParadigmsCorrect.lambda c))
    ; lambda≈ethereum = λ t →
        let c = patask-paradigms-correct t in
        trans (ParadigmsCorrect.lambda c)
              (sym (ParadigmsCorrect.ethereum c))
    ; ethereum≈oracle = λ t →
        let c = patask-paradigms-correct t in
        trans (ParadigmsCorrect.ethereum c)
              (sym (ParadigmsCorrect.oracle c))
    ; oracle≈circuit = λ t →
        let c = patask-paradigms-correct t in
        trans (ParadigmsCorrect.oracle c)
              (sym (ParadigmsCorrect.circuit c))
    }

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).
--
-- Computational universality is presented as a “machines as schemes” pack:
-- one algorithmic meaning, many implementation schemes, plus explicit
-- agreement witnesses.

record Assumptions : Set₁ where
  constructor mkAssumptions

record Claim (_ : Assumptions) : Set₁ where
  field
    Alg : Sch.Algorithm PATask ℕ

    -- Scheme implementations (universal carrier `UCode`).
    minsky   : Sch.ImplementsRun Alg minskyScheme
    lambda   : Sch.ImplementsRun Alg lambdaScheme
    ethereum : Sch.ImplementsRun Alg ethereumScheme
    oracle   : Sch.ImplementsRun Alg oracleScheme
    circuit  : Sch.ImplementsRun Alg quantumCircuitScheme

    -- Cost honesty: each representation runs within the universal (3n,n) envelope
    -- induced by its chosen fuel bound.
    minskyCost   : ∀ t → Sch.Scheme._≤s_ minskyScheme (Sch.cost minskyScheme t) (fuelBudgetFor minskyScheme t)
    lambdaCost   : ∀ t → Sch.Scheme._≤s_ lambdaScheme (Sch.cost lambdaScheme t) (fuelBudgetFor lambdaScheme t)
    ethereumCost : ∀ t → Sch.Scheme._≤s_ ethereumScheme (Sch.cost ethereumScheme t) (fuelBudgetFor ethereumScheme t)
    oracleCost   : ∀ t → Sch.Scheme._≤s_ oracleScheme (Sch.cost oracleScheme t) (fuelBudgetFor oracleScheme t)
    circuitCost  : ∀ t → Sch.Scheme._≤s_ quantumCircuitScheme (Sch.cost quantumCircuitScheme t) (fuelBudgetFor quantumCircuitScheme t)

    -- Meaning agreement across schemes.
    minsky≈lambda   : Sch.RunEq minskyScheme lambdaScheme
    lambda≈ethereum : Sch.RunEq lambdaScheme ethereumScheme
    ethereum≈oracle : Sch.RunEq ethereumScheme oracleScheme
    oracle≈circuit  : Sch.RunEq oracleScheme quantumCircuitScheme

module Q = AppKit.MakeDerived Assumptions Claim
  (λ _ →
    record
      { Alg            = PAAlg
      ; minsky         = minsky-implements-PA
      ; lambda         = lambda-implements-PA
      ; ethereum       = ethereum-implements-PA
      ; oracle         = oracle-implements-PA
      ; circuit        = circuit-implements-PA
      ; minskyCost     = λ t → ChoiceSchemesCostBound.minsky (patask-choiceSchemes-costBound t)
      ; lambdaCost     = λ t → ChoiceSchemesCostBound.lambda (patask-choiceSchemes-costBound t)
      ; ethereumCost   = λ t → ChoiceSchemesCostBound.ethereum (patask-choiceSchemes-costBound t)
      ; oracleCost     = λ t → ChoiceSchemesCostBound.oracle (patask-choiceSchemes-costBound t)
      ; circuitCost    = λ t → ChoiceSchemesCostBound.circuit (patask-choiceSchemes-costBound t)
      ; minsky≈lambda   = ChoiceSchemesRunEq.minsky≈lambda patask-choiceSchemes-runEq
      ; lambda≈ethereum = ChoiceSchemesRunEq.lambda≈ethereum patask-choiceSchemes-runEq
      ; ethereum≈oracle = ChoiceSchemesRunEq.ethereum≈oracle patask-choiceSchemes-runEq
      ; oracle≈circuit  = ChoiceSchemesRunEq.oracle≈circuit patask-choiceSchemes-runEq
      })
open Q public using (Pack; assumptionsOf; claimOf; mkPack)
