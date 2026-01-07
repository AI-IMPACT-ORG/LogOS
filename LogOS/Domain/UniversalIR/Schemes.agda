{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Schemes where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import LogOS.QAdapters.QNat2 using (QNat2)
open import LogOS.QAdapters.QNat2 as Q2 using (scaleOps; steps-budget-τ; μ; μ-+; μ-zero; τ-mono; μ-mono)
open import Data.NatExtra using (⊔ℕ-zeroʳ)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Minimal.ScaleOps using (ScaleOps)
open import LogOS.Computation.Scheme using (Scheme; Closure)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

import LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp

open import LogOS.Domain.UniversalIR.Core
  using
    ( QScalars
    ; UCode; UM; UL; UE; UQ; UQC
    ; stepU; simulate
    ; MinskyCode; stepM; MInstr; HALT; INC; DECJZ
    ; EVMCode; stepE; EInstr; STOP; PUSH; ADD; MUL; POP; SUB; DUP; SWAP; JUMP; JUMPI; MLOAD; MSTORE
    ; LambdaCode; stepLC
    ; QInstr; QHALT; QINC; QDECJZ; MEASURE
    ; QuantumCode; stepQ
    ; QCInstr; QCHALT; QNOP; QX; QCNOT; QTOFF; QMEASURE
    ; QuantumCircuitCode; stepQC
    ; lookupDefault
    )
open import LogOS.Domain.UniversalIR.IR using (lowerToIR; observe)
open import LogOS.Domain.UniversalIR.Task using (PATask)
open import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
open import LogOS.Domain.UniversalIR.Languages.Lambda as Lambda
open import LogOS.Domain.UniversalIR.Languages.Ethereum as Ethereum
open import LogOS.Domain.UniversalIR.Languages.QuantumOracle as QuantumOracle
open import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as QuantumCircuit
open import LogOS.Computation.Core using (iterate)

-- The canonical cost adapter for the UniversalIR scheme layer.
--
-- `QNat2` is a two-axis (finite-join) quantale on `ℕ × ℕ`:
-- - axis 1: ordinary/unitary work (steps, gas, gate-count, …)
-- - axis 2: non-unitary events (measurement/classicalization)

QSteps = QNat2

open QAdapter QSteps using (τ; _⊔s_; _≤s_; ≤s-trans; ⊔s-ub₁; ⊔s-ub₂; ⊔s-least; _·_; e; ·-mono)

OpsSteps : ScaleOps QSteps
OpsSteps = Q2.scaleOps

Budget : Set lzero
Budget = QAdapter.Scale QSteps

-- Cost helpers (two-axis quantale split)
--
-- In `QNat2`, `Scale = ℕ × ℕ` with componentwise order and join:
-- - first axis: ordinary/unitary work (steps, gates, gas-like)
-- - second axis: non-unitary events (measurement/classicalization)

work : ℕ → Budget
work = τ

meas : ℕ → Budget
meas = μ

-- Measurement-axis algebra (the second axis is additive under quantale
-- multiplication, and has `e` as its zero).

work-zero : work zero ≡ e
work-zero = QAdapter.τ-zero QSteps

work-+ : ∀ n m → work (n + m) ≡ (work n · work m)
work-+ = QAdapter.τ-+ QSteps

meas-zero : meas zero ≡ e
meas-zero = Q2.μ-zero

meas-+ : ∀ n m → meas (n + m) ≡ (meas n · meas m)
meas-+ = Q2.μ-+

work-mono : ∀ {n m} → n ≤ℕ m → work n ≤s work m
work-mono = Q2.τ-mono

meas-mono : ∀ {n m} → n ≤ℕ m → meas n ≤s meas m
meas-mono = Q2.μ-mono

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

one≤three : one ≤ℕ three
one≤three = s≤s z≤n

two≤three : two ≤ℕ three
two≤three = s≤s (s≤s z≤n)

-- Join composes orthogonal budgets: a step budget and a measurement budget.
--
-- This makes the quantale structure operational in the universality story:
-- you can state “compute within k steps and at most m measurements” as a single
-- grade value (`k` on axis 1, `m` on axis 2).

budget₂ : ℕ → ℕ → Budget
budget₂ k m = work k ⊔s meas m

-- In `QNat2`, the orthogonal join budget is literally the pair `(k , m)`:
-- one can bound unitary work and non-unitary measurement independently.
budget₂≡pair : ∀ k m → budget₂ k m ≡ (k , m)
budget₂≡pair k m
  rewrite ⊔ℕ-zeroʳ k
  = refl

-- Time/step interpretation: `ScaleOps` reads the work axis only.
budget-budget₂ : ∀ k m → ScaleOps.budget OpsSteps (budget₂ k m) ≡ k
budget-budget₂ k m
  rewrite ⊔ℕ-zeroʳ k
  = refl

steps-budget₂ : ∀ k m → ScaleOps.steps OpsSteps (ScaleOps.budget OpsSteps (budget₂ k m)) ≡ k
steps-budget₂ k m
  rewrite ⊔ℕ-zeroʳ k
  = refl

work≤budget₂ : ∀ k m → work k ≤s budget₂ k m
work≤budget₂ k m = ⊔s-ub₁ (work k) (meas m)

meas≤budget₂ : ∀ k m → meas m ≤s budget₂ k m
meas≤budget₂ k m = ⊔s-ub₂ (work k) (meas m)

-- Orthogonality (sanity): measurement cannot be “paid for” by work-only budget,
-- and vice versa. This is the formal, concrete version of “time and
-- classicalization capacity are independent axes”.
meas1≰work : ∀ k → ¬ (meas one ≤s work k)
meas1≰work k (_ , ())

work1≰meas : ∀ m → ¬ (work one ≤s meas m)
work1≰meas m (() , _)

-- UniversalIR normalisation preorder: two codes are “renormalisation-equivalent”
-- when they agree after lowering to the canonical IR branch.

infix 4 _⊑ᵁ_

_⊑ᵁ_ : UCode → UCode → Set
u ⊑ᵁ v = lowerToIR u ≡ lowerToIR v

CPᵁ : ConPoset lzero
CPᵁ = record
  { Con  = UCode
  ; _⊑_  = _⊑ᵁ_
  ; refl = refl
  ; trans = trans
  }

-- Plan B semantics center: keep the closure trivial, and push canonicalisation
-- into the observation function `observeU`.
--
-- This makes it easy to treat each concrete paradigm as a *scheme* in its own
-- right (its own state + step + cost profile) while still sharing the same
-- observable meaning as the universal process.

IdNormᵁ : Closure CPᵁ
IdNormᵁ = record
  { cl        = λ u → u
  ; mono      = λ {u} {v} eq → eq
  ; infl      = λ _ → refl
  ; idemp-lax = λ _ → refl
  }

observeU : UCode → ℕ
observeU = observe

-- A non-trivial quantale-cost profile (e.g. “gas”) for the universal carrier.
-- These weights are intentionally simple and purely structural: they show how
-- the quantale algebra composes costs across heterogeneous machine steps.

costMInstr : MInstr → ℕ
costMInstr HALT       = zero
costMInstr (INC _ _)  = one
costMInstr (DECJZ _ _ _) = one

costMInstr≤one : ∀ i → costMInstr i ≤ℕ one
costMInstr≤one HALT = z≤n
costMInstr≤one (INC _ _) = ≤ℕ-refl
costMInstr≤one (DECJZ _ _ _) = ≤ℕ-refl

stepCostM : MinskyCode → Budget
stepCostM m = work (costMInstr (lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m)))

stepCostM≤work1 : ∀ m → stepCostM m ≤s work one
stepCostM≤work1 m =
  work-mono (costMInstr≤one (lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m)))

gas : EInstr → ℕ
gas STOP      = one
gas (PUSH _)  = one
gas POP       = one
gas ADD       = one
gas MUL       = two
gas SUB       = one
gas DUP       = one
gas SWAP      = one
gas JUMP      = two
gas JUMPI     = two
gas MLOAD     = three
gas MSTORE    = three

gas≤three : ∀ i → gas i ≤ℕ three
gas≤three STOP = s≤s z≤n
gas≤three (PUSH _) = s≤s z≤n
gas≤three POP = s≤s z≤n
gas≤three ADD = s≤s z≤n
gas≤three MUL = s≤s (s≤s z≤n)
gas≤three SUB = s≤s z≤n
gas≤three DUP = s≤s z≤n
gas≤three SWAP = s≤s z≤n
gas≤three JUMP = s≤s (s≤s z≤n)
gas≤three JUMPI = s≤s (s≤s z≤n)
gas≤three MLOAD = ≤ℕ-refl
gas≤three MSTORE = ≤ℕ-refl

stepCostE : EVMCode → Budget
stepCostE e = work (gas (lookupDefault STOP (EVMCode.code e) (EVMCode.pc e)))

stepCostE≤work3 : ∀ e → stepCostE e ≤s work three
stepCostE≤work3 e =
  work-mono (gas≤three (lookupDefault STOP (EVMCode.code e) (EVMCode.pc e)))

-- Quantum costs: measure dominates the nonunitary axis.
costQInstr : QInstr → Budget
costQInstr QHALT = work zero
costQInstr (QINC _ _) = work one
costQInstr (QDECJZ _ _ _) = work one
costQInstr (MEASURE _ _ _) = meas one

costQInstr≤budget11 : ∀ i → costQInstr i ≤s budget₂ one one
costQInstr≤budget11 QHALT =
  ≤s-trans (work-mono z≤n) (work≤budget₂ one one)
costQInstr≤budget11 (QINC _ _) = work≤budget₂ one one
costQInstr≤budget11 (QDECJZ _ _ _) = work≤budget₂ one one
costQInstr≤budget11 (MEASURE _ _ _) = meas≤budget₂ one one

stepCostQ : QuantumCode → Budget
stepCostQ q = costQInstr (lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q))

stepCostQ≤budget11 : ∀ q → stepCostQ q ≤s budget₂ one one
stepCostQ≤budget11 q =
  costQInstr≤budget11 (lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q))

costQCInstr : QCInstr → Budget
costQCInstr QCHALT = work zero
costQCInstr QNOP = work one
costQCInstr (QX _) = work one
costQCInstr (QCNOT _ _) = work one
costQCInstr (QTOFF _ _ _) = work two
costQCInstr (QMEASURE _ _ _) = meas one

costQCInstr≤budget21 : ∀ i → costQCInstr i ≤s budget₂ two one
costQCInstr≤budget21 QCHALT =
  ≤s-trans (work-mono z≤n) (work≤budget₂ two one)
costQCInstr≤budget21 QNOP =
  ≤s-trans (work-mono (s≤s z≤n)) (work≤budget₂ two one)
costQCInstr≤budget21 (QX _) =
  ≤s-trans (work-mono (s≤s z≤n)) (work≤budget₂ two one)
costQCInstr≤budget21 (QCNOT _ _) =
  ≤s-trans (work-mono (s≤s z≤n)) (work≤budget₂ two one)
costQCInstr≤budget21 (QTOFF _ _ _) = work≤budget₂ two one
costQCInstr≤budget21 (QMEASURE _ _ _) = meas≤budget₂ two one

stepCostQC : QuantumCircuitCode → Budget
stepCostQC q = costQCInstr (lookupDefault QCHALT (QuantumCircuitCode.prog q) (QuantumCircuitCode.pc q))

stepCostQC≤budget21 : ∀ q → stepCostQC q ≤s budget₂ two one
stepCostQC≤budget21 q =
  costQCInstr≤budget21 (lookupDefault QCHALT (QuantumCircuitCode.prog q) (QuantumCircuitCode.pc q))

stepCostᵁ : UCode → Budget
stepCostᵁ (UM m)  = stepCostM m
stepCostᵁ (UL _)  = work one
stepCostᵁ (UE e)  = stepCostE e
stepCostᵁ (UQ q)  = stepCostQ q
stepCostᵁ (UQC q) = stepCostQC q

-- A single “per-step envelope” for the whole `UCode` coproduct.
--
-- This is where the finite-join quantale structure starts to pay off: the
-- universal stepper contains heterogeneous instructions (Minsky, EVM, quantum),
-- but they all fit under one explicit (work ⊔ measurement) budget.

stepBudgetᵁ : Budget
stepBudgetᵁ = budget₂ three one

work1≤stepBudgetᵁ : work one ≤s stepBudgetᵁ
work1≤stepBudgetᵁ = ≤s-trans (work-mono one≤three) (work≤budget₂ three one)

work2≤stepBudgetᵁ : work two ≤s stepBudgetᵁ
work2≤stepBudgetᵁ = ≤s-trans (work-mono two≤three) (work≤budget₂ three one)

work3≤stepBudgetᵁ : work three ≤s stepBudgetᵁ
work3≤stepBudgetᵁ = work≤budget₂ three one

meas1≤stepBudgetᵁ : meas one ≤s stepBudgetᵁ
meas1≤stepBudgetᵁ = meas≤budget₂ three one

budget11≤stepBudgetᵁ : budget₂ one one ≤s stepBudgetᵁ
budget11≤stepBudgetᵁ = ⊔s-least work1≤stepBudgetᵁ meas1≤stepBudgetᵁ

budget21≤stepBudgetᵁ : budget₂ two one ≤s stepBudgetᵁ
budget21≤stepBudgetᵁ = ⊔s-least work2≤stepBudgetᵁ meas1≤stepBudgetᵁ

stepCostM≤stepBudgetᵁ : ∀ m → stepCostM m ≤s stepBudgetᵁ
stepCostM≤stepBudgetᵁ m = ≤s-trans (stepCostM≤work1 m) work1≤stepBudgetᵁ

stepCostE≤stepBudgetᵁ : ∀ e → stepCostE e ≤s stepBudgetᵁ
stepCostE≤stepBudgetᵁ e = ≤s-trans (stepCostE≤work3 e) work3≤stepBudgetᵁ

stepCostQ≤stepBudgetᵁ : ∀ q → stepCostQ q ≤s stepBudgetᵁ
stepCostQ≤stepBudgetᵁ q = ≤s-trans (stepCostQ≤budget11 q) budget11≤stepBudgetᵁ

stepCostQC≤stepBudgetᵁ : ∀ q → stepCostQC q ≤s stepBudgetᵁ
stepCostQC≤stepBudgetᵁ q = ≤s-trans (stepCostQC≤budget21 q) budget21≤stepBudgetᵁ

stepCostᵁ≤stepBudgetᵁ : ∀ u → stepCostᵁ u ≤s stepBudgetᵁ
stepCostᵁ≤stepBudgetᵁ (UM m)  = stepCostM≤stepBudgetᵁ m
stepCostᵁ≤stepBudgetᵁ (UL _)  = work1≤stepBudgetᵁ
stepCostᵁ≤stepBudgetᵁ (UE e)  = stepCostE≤stepBudgetᵁ e
stepCostᵁ≤stepBudgetᵁ (UQ q)  = stepCostQ≤stepBudgetᵁ q
stepCostᵁ≤stepBudgetᵁ (UQC q) = stepCostQC≤stepBudgetᵁ q

-- ============================================================================
-- Universal computation as a shared process + paradigm choices
--
-- The universal dynamics is the `UCode` stepper + IR-normalisation. Concrete
-- paradigms are *choices* (compiler + fuel) into this shared process.
-- ============================================================================

UProcess : Cat.Process ℕ
UProcess =
  record
    { CP       = CPᵁ
    ; Step     = stepU
    ; Norm     = IdNormᵁ
    ; decode   = observeU
    ; Q        = QSteps
    ; stepCost = stepCostᵁ
    }

-- Iterated envelope: the cost of n steps is bounded by n-fold multiplication of
-- the per-step envelope.

stepBudgetPowᵁ : ℕ → Budget
stepBudgetPowᵁ zero    = e
stepBudgetPowᵁ (suc n) = stepBudgetᵁ · stepBudgetPowᵁ n

costExecPᵁ≤stepBudgetPowᵁ
  : ∀ n u
  → QAdapter._≤s_ QSteps (Cat.costExecP UProcess n u) (stepBudgetPowᵁ n)
costExecPᵁ≤stepBudgetPowᵁ zero    _ = QAdapter.≤s-refl QSteps
costExecPᵁ≤stepBudgetPowᵁ (suc n) u =
  ·-mono (stepCostᵁ≤stepBudgetᵁ u)
         (costExecPᵁ≤stepBudgetPowᵁ n (stepU u))

-- Closed-form envelope: for `n` steps, the maximal cost is linear in `n` on both
-- axes (≤ 3 work-units per step, ≤ 1 measurement per step).
--
-- We define `3n` by the same recursion as the envelope itself (avoids relying on
-- host-level multiplication primitives).

three· : ℕ → ℕ
three· zero    = zero
three· (suc n) = three + three· n

private
  stepBudgetᵁ≡pair : stepBudgetᵁ ≡ (three , one)
  stepBudgetᵁ≡pair = budget₂≡pair three one

  stepBudgetPowᵁ≡pair : ∀ n → stepBudgetPowᵁ n ≡ (three· n , n)
  stepBudgetPowᵁ≡pair zero    = refl
  stepBudgetPowᵁ≡pair (suc n)
    rewrite stepBudgetᵁ≡pair
          | stepBudgetPowᵁ≡pair n
    = refl

stepBudgetPowᵁ≡budget₂3n,n : ∀ n → stepBudgetPowᵁ n ≡ budget₂ (three· n) n
stepBudgetPowᵁ≡budget₂3n,n zero = refl
stepBudgetPowᵁ≡budget₂3n,n (suc n)
  rewrite stepBudgetPowᵁ≡pair (suc n)
        | budget₂≡pair (three· (suc n)) (suc n)
  = refl

costExecPᵁ≤budget₂3n,n
  : ∀ n u
  → QAdapter._≤s_ QSteps (Cat.costExecP UProcess n u) (budget₂ (three· n) n)
costExecPᵁ≤budget₂3n,n n u =
  subst
    (λ b → QAdapter._≤s_ QSteps (Cat.costExecP UProcess n u) b)
    (stepBudgetPowᵁ≡budget₂3n,n n)
    (costExecPᵁ≤stepBudgetPowᵁ n u)

-- Scheme-level cost envelope for any choice into the universal process.
--
-- This bridges the scheme interface (`Sch.cost`) to the process-level envelope
-- (`costExecPᵁ≤budget₂3n,n`) without assuming definitional equality.

costExecP≡costExecᵁ
  : ∀ {ℓI} {Input : Set ℓI}
    (C : Cat.Choice Input UProcess)
  → ∀ n u
  → Cat.costExecP UProcess n u ≡ Sch.Scheme.costExec (Cat.schemeFromChoice UProcess C) n u
costExecP≡costExecᵁ _ zero    _ = refl
costExecP≡costExecᵁ C (suc n) u =
  cong (stepCostᵁ u ·_) (costExecP≡costExecᵁ C n (stepU u))

costExecᵁ≤budget₂3n,n
  : ∀ {ℓI} {Input : Set ℓI}
    (C : Cat.Choice Input UProcess)
  → ∀ n u
  → QAdapter._≤s_ QSteps (Sch.Scheme.costExec (Cat.schemeFromChoice UProcess C) n u) (budget₂ (three· n) n)
costExecᵁ≤budget₂3n,n C n u =
  subst
    (λ c → QAdapter._≤s_ QSteps c (budget₂ (three· n) n))
    (costExecP≡costExecᵁ C n u)
    (costExecPᵁ≤budget₂3n,n n u)

choiceScheme-cost≤budget₂3n,n
  : ∀ {ℓI} {Input : Set ℓI}
    (C : Cat.Choice Input UProcess)
  → ∀ x
  → QAdapter._≤s_ QSteps (Sch.cost (Cat.schemeFromChoice UProcess C) x)
      (budget₂ (three· (Cat.Choice.fuel C x)) (Cat.Choice.fuel C x))
choiceScheme-cost≤budget₂3n,n C x =
  costExecᵁ≤budget₂3n,n C (Cat.Choice.fuel C x) (Cat.Choice.compile C x)

-- ============================================================================
-- Budgeted execution (quantale-graded, compositional)
--
-- `choiceScheme-cost≤budget₂3n,n` bounds the *total* fuel-bounded run cost.
-- With `QAdapter.·-mono` available, we can also expose a more operational view:
-- budgeted executions compose under quantale multiplication.
-- ============================================================================

choiceScheme-execWithinAt≤budget₂3n,n
  : ∀ {ℓI} {Input : Set ℓI}
    (C : Cat.Choice Input UProcess)
  → ∀ x
  → Sch.ExecWithin
      (Cat.schemeFromChoice UProcess C)
      (Cat.Choice.fuel C x)
      (Cat.Choice.compile C x)
      (budget₂ (three· (Cat.Choice.fuel C x)) (Cat.Choice.fuel C x))
      (Sch.exec (Cat.schemeFromChoice UProcess C) (Cat.Choice.fuel C x) x)
choiceScheme-execWithinAt≤budget₂3n,n C x =
  LogOS.Prelude.refl ,
  costExecᵁ≤budget₂3n,n C (Cat.Choice.fuel C x) (Cat.Choice.compile C x)

choiceScheme-execWithinSplit≤budget₂3n,n
  : ∀ {ℓI} {Input : Set ℓI}
    (C : Cat.Choice Input UProcess)
  → ∀ m n u
  → Sch.ExecWithin
      (Cat.schemeFromChoice UProcess C)
      (m + n)
      u
      (budget₂ (three· m) m · budget₂ (three· n) n)
      (iterate (Sch.Scheme.Comp (Cat.schemeFromChoice UProcess C)) n
        (iterate (Sch.Scheme.Comp (Cat.schemeFromChoice UProcess C)) m u))
choiceScheme-execWithinSplit≤budget₂3n,n C m n u =
  Sch.ExecWithin-+
    S
    {m = m}
    {n = n}
    {c = u}
    {c₁ = iterate CompS m u}
    {c₂ = iterate CompS n (iterate CompS m u)}
    {b = budget₂ (three· m) m}
    {d = budget₂ (three· n) n}
    ew₁ ew₂
  where
    S = Cat.schemeFromChoice UProcess C
    CompS = Sch.Scheme.Comp S

    ew₁ : Sch.ExecWithin S m u (budget₂ (three· m) m) (iterate CompS m u)
    ew₁ = LogOS.Prelude.refl , costExecᵁ≤budget₂3n,n C m u

    ew₂
      : Sch.ExecWithin S n (iterate CompS m u) (budget₂ (three· n) n)
          (iterate CompS n (iterate CompS m u))
    ew₂ = LogOS.Prelude.refl , costExecᵁ≤budget₂3n,n C n (iterate CompS m u)

-- Scale-indexed execution (machines as schemes):
-- running within a grade `g` means iterating for `steps (budget g)` steps.
run≤ᵁ : Cat.Process.Scale UProcess → UCode → UCode
run≤ᵁ = Cat.run≤ UProcess OpsSteps

-- Independence of the measurement axis (concrete, QNat2):
-- the induced execution trace depends only on the work axis `k`.
run≤ᵁ-budget₂≡work
  : ∀ k m u → run≤ᵁ (budget₂ k m) u ≡ run≤ᵁ (work k) u
run≤ᵁ-budget₂≡work k m u =
  Cat.run≤-stepsEq UProcess OpsSteps {g = budget₂ k m} {g' = work k} u
    (LogOS.Prelude.trans (steps-budget₂ k m) (sym (steps-budget-τ k)))

-- The original `Sch.run` for each scheme uses a chosen `fuel : Input → ℕ`.
-- Under `QNat2.scaleOps`, `fuel` is exactly the step budget induced by the
-- grade `work (fuel t)` (second axis is measurement-only).
fuelGrade : (fuel : PATask → ℕ) → PATask → Cat.Process.Scale UProcess
fuelGrade fuel t = work (fuel t)

mkChoice
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (P : Cat.Process {ℓO} {ℓC} {ℓQ} Output)
    → (Input → Cat.Process.Con P)
    → (Input → ℕ)
    → Cat.Choice Input P
mkChoice _ compile fuel = record { compile = compile ; fuel = fuel }

mkScheme
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (P : Cat.Process {ℓO} {ℓC} {ℓQ} Output)
    → (Input → Cat.Process.Con P)
    → (Input → ℕ)
    → Scheme Input Output
mkScheme P compile fuel = Cat.schemeFromChoice P (mkChoice P compile fuel)

minskyChoice : Cat.Choice PATask UProcess
minskyChoice = mkChoice UProcess Minsky.compile Minsky.fuel

lambdaChoice : Cat.Choice PATask UProcess
lambdaChoice = mkChoice UProcess Lambda.compile Lambda.fuel

ethereumChoice : Cat.Choice PATask UProcess
ethereumChoice = mkChoice UProcess Ethereum.compile Ethereum.fuel

oracleChoice : Cat.Choice PATask UProcess
oracleChoice = mkChoice UProcess QuantumOracle.compile QuantumOracle.fuel

quantumCircuitChoice : Cat.Choice PATask UProcess
quantumCircuitChoice = mkChoice UProcess QuantumCircuit.compile QuantumCircuit.fuel

-- Five concrete “representation schemes” for the same PATask meaning.
-- (Same process, different choices.)

minskyScheme : Scheme PATask ℕ
minskyScheme = mkScheme UProcess Minsky.compile Minsky.fuel

lambdaScheme : Scheme PATask ℕ
lambdaScheme = mkScheme UProcess Lambda.compile Lambda.fuel

ethereumScheme : Scheme PATask ℕ
ethereumScheme = mkScheme UProcess Ethereum.compile Ethereum.fuel

oracleScheme : Scheme PATask ℕ
oracleScheme = mkScheme UProcess QuantumOracle.compile QuantumOracle.fuel

quantumCircuitScheme : Scheme PATask ℕ
quantumCircuitScheme = mkScheme UProcess QuantumCircuit.compile QuantumCircuit.fuel

-- Scale-indexed execution for each scheme (grade → step budget via `ScaleOps`).
--
-- These are the entrypoints to state “same computation under budget g” across
-- representations, without baking a per-paradigm fuel function into the meaning.
run≤-minsky : Cat.Process.Scale UProcess → PATask → ℕ
run≤-minsky g t = Sch.run≤ minskyScheme OpsSteps g t

run≤-lambda : Cat.Process.Scale UProcess → PATask → ℕ
run≤-lambda g t = Sch.run≤ lambdaScheme OpsSteps g t

run≤-ethereum : Cat.Process.Scale UProcess → PATask → ℕ
run≤-ethereum g t = Sch.run≤ ethereumScheme OpsSteps g t

run≤-oracle : Cat.Process.Scale UProcess → PATask → ℕ
run≤-oracle g t = Sch.run≤ oracleScheme OpsSteps g t

run≤-quantumCircuit : Cat.Process.Scale UProcess → PATask → ℕ
run≤-quantumCircuit g t = Sch.run≤ quantumCircuitScheme OpsSteps g t

-- Special case: the schedule-based `Sch.run` (with schedule `fuel`) is the same
-- as `run≤-*` at grade `work (fuel t)` (i.e. `τ (fuel t)` in `QNat2`).

run≤-fuel≡run-choice
  : ∀ (C : Cat.Choice PATask UProcess) (t : PATask)
  → Sch.run≤ (Cat.schemeFromChoice UProcess C) OpsSteps (fuelGrade (Cat.Choice.fuel C) t) t
    ≡ Sch.run (Cat.schemeFromChoice UProcess C) t
run≤-fuel≡run-choice C t =
  cong
    (λ k → Sch.decode S (Sch.normalize S (Sch.exec S k t)))
    (sym (Q2.steps-budget-τ (Cat.Choice.fuel C t)))
  where
    S = Cat.schemeFromChoice UProcess C

run≤-fuel≡run-minsky : ∀ t → run≤-minsky (fuelGrade Minsky.fuel t) t ≡ Sch.run minskyScheme t
run≤-fuel≡run-minsky t = run≤-fuel≡run-choice minskyChoice t

run≤-fuel≡run-lambda : ∀ t → run≤-lambda (fuelGrade Lambda.fuel t) t ≡ Sch.run lambdaScheme t
run≤-fuel≡run-lambda t = run≤-fuel≡run-choice lambdaChoice t

run≤-fuel≡run-ethereum : ∀ t → run≤-ethereum (fuelGrade Ethereum.fuel t) t ≡ Sch.run ethereumScheme t
run≤-fuel≡run-ethereum t = run≤-fuel≡run-choice ethereumChoice t

run≤-fuel≡run-oracle : ∀ t → run≤-oracle (fuelGrade QuantumOracle.fuel t) t ≡ Sch.run oracleScheme t
run≤-fuel≡run-oracle t = run≤-fuel≡run-choice oracleChoice t

run≤-fuel≡run-quantumCircuit
  : ∀ t → run≤-quantumCircuit (fuelGrade QuantumCircuit.fuel t) t ≡ Sch.run quantumCircuitScheme t
run≤-fuel≡run-quantumCircuit t = run≤-fuel≡run-choice quantumCircuitChoice t

-- ============================================================================
-- “Machines are schemes”: each paradigm can be presented as its own scheme
-- (own state + own step + own cost profile) and mapped into the universal one.
--
-- The universal process is the semantic center; concrete machines are just
-- presentations with their own resource/cost models.
-- ============================================================================

EqCP : ∀ {ℓ} (A : Set ℓ) → ConPoset ℓ
EqCP A = record { Con = A ; _⊑_ = _≡_ ; refl = refl ; trans = trans }

IdClosure : ∀ {ℓ} (CP : ConPoset ℓ) → Closure CP
IdClosure CP = record
  { cl        = λ c → c
  ; mono      = λ p → p
  ; infl      = λ _ → ConPoset.refl CP
  ; idemp-lax = λ _ → ConPoset.refl CP
  }

MinskyProcess : Cat.Process ℕ
MinskyProcess =
  record
    { CP       = EqCP MinskyCode
    ; Step     = stepM
    ; Norm     = IdClosure (EqCP MinskyCode)
    ; decode   = λ m → observeU (UM m)
    ; Q        = QSteps
    ; stepCost = stepCostM
    }

-- “One-stroke” coverage of Minsky variants:
-- any alternative resource accounting (step-cost function) for the same Minsky
-- small-step semantics can be wrapped as a `Process` and still factors through
-- the universal semantic center via the same injection `UM`.

MinskyProcessWith : (MinskyCode → Budget) → Cat.Process ℕ
MinskyProcessWith stepCost =
  record
    { CP       = EqCP MinskyCode
    ; Step     = stepM
    ; Norm     = IdClosure (EqCP MinskyCode)
    ; decode   = λ m → observeU (UM m)
    ; Q        = QSteps
    ; stepCost = stepCost
    }

Minsky→U-With : ∀ stepCost → Cat.ProcessHom (MinskyProcessWith stepCost) UProcess
Minsky→U-With _ =
  record
    { map        = UM
    ; mono       = λ {refl → refl}
    ; step-comm  = λ _ → refl
    ; norm-comm  = λ _ → refl
    ; decode-comm = λ _ → refl
    }

EthereumProcess : Cat.Process ℕ
EthereumProcess =
  record
    { CP       = EqCP EVMCode
    ; Step     = stepE
    ; Norm     = IdClosure (EqCP EVMCode)
    ; decode   = λ e → observeU (UE e)
    ; Q        = QSteps
    ; stepCost = stepCostE
    }

LambdaProcess : Cat.Process ℕ
LambdaProcess =
  record
    { CP       = EqCP LambdaCode
    ; Step     = stepLC
    ; Norm     = IdClosure (EqCP LambdaCode)
    ; decode   = λ l → observeU (UL l)
    ; Q        = QSteps
    ; stepCost = λ _ → work one
    }

QuantumOracleProcess : Cat.Process ℕ
QuantumOracleProcess =
  record
    { CP       = EqCP QuantumCode
    ; Step     = stepQ
    ; Norm     = IdClosure (EqCP QuantumCode)
    ; decode   = λ q → observeU (UQ q)
    ; Q        = QSteps
    ; stepCost = stepCostQ
    }

QuantumCircuitProcess : Cat.Process ℕ
QuantumCircuitProcess =
  record
    { CP       = EqCP QuantumCircuitCode
    ; Step     = stepQC
    ; Norm     = IdClosure (EqCP QuantumCircuitCode)
    ; decode   = λ q → observeU (UQC q)
    ; Q        = QSteps
    ; stepCost = stepCostQC
    }

module QuantumCircuitAmpSchemes {ℓ} (S : QScalars {ℓ}) where
  module A = LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp.For S

  open QScalars S using (Carrier)
  open A using (QuantumCircuitAmpPCode; QCInstrP; DistList; Wires; stepDistQCA; observeDistList)
  open A.QuantumCircuitAmpPCode using (pc; prog)
  open A.DistList using (support)

  costQCAInstr : ∀ {n} → QCInstrP n → Budget
  costQCAInstr A.QCHALT = work zero
  costQCAInstr (A.QX _) = work one
  costQCAInstr (A.QH _) = work one
  costQCAInstr (A.QCNOT _ _) = work one
  costQCAInstr (A.QTOFF _ _ _) = work two
  costQCAInstr (A.QMEASURE _ _ _) = meas one

  stepCostQCA : ∀ {n} → QuantumCircuitAmpPCode n → Budget
  stepCostQCA q = costQCAInstr (lookupDefault A.QCHALT (prog q) (pc q))

  joinSupport : ∀ {n} → List (Carrier × QuantumCircuitAmpPCode n) → Budget
  joinSupport [] = e
  joinSupport ((_ , q) ∷ xs) = stepCostQCA q ⊔s joinSupport xs

  stepCostDistQCA : ∀ {n} → DistList (QuantumCircuitAmpPCode n) → Budget
  stepCostDistQCA d = joinSupport (support d)

  QuantumCircuitAmpProcess : ∀ {n} → Cat.Process (DistList (Wires n))
  QuantumCircuitAmpProcess {n} =
    record
      { CP       = EqCP (DistList (QuantumCircuitAmpPCode n))
      ; Step     = stepDistQCA
      ; Norm     = IdClosure (EqCP (DistList (QuantumCircuitAmpPCode n)))
      ; decode   = observeDistList
      ; Q        = QSteps
      ; stepCost = stepCostDistQCA
      }

module QuantumCircuitAmpFree where
  open import LogOS.Domain.UniversalIR.Quantum.Scalars.Free using (formalScalars)
  open QuantumCircuitAmpSchemes formalScalars public

minskyMachineChoice : Cat.Choice PATask MinskyProcess
minskyMachineChoice = mkChoice MinskyProcess Minsky.compileBrand Minsky.fuel

ethereumMachineChoice : Cat.Choice PATask EthereumProcess
ethereumMachineChoice = mkChoice EthereumProcess Ethereum.compileBrand Ethereum.fuel

lambdaMachineChoice : Cat.Choice PATask LambdaProcess
lambdaMachineChoice = mkChoice LambdaProcess Lambda.compileBrand Lambda.fuel

oracleMachineChoice : Cat.Choice PATask QuantumOracleProcess
oracleMachineChoice = mkChoice QuantumOracleProcess QuantumOracle.compileBrand QuantumOracle.fuel

quantumCircuitMachineChoice : Cat.Choice PATask QuantumCircuitProcess
quantumCircuitMachineChoice = mkChoice QuantumCircuitProcess QuantumCircuit.compileBrand QuantumCircuit.fuel

minskyMachineScheme : Scheme PATask ℕ
minskyMachineScheme = mkScheme MinskyProcess Minsky.compileBrand Minsky.fuel

ethereumMachineScheme : Scheme PATask ℕ
ethereumMachineScheme = mkScheme EthereumProcess Ethereum.compileBrand Ethereum.fuel

lambdaMachineScheme : Scheme PATask ℕ
lambdaMachineScheme = mkScheme LambdaProcess Lambda.compileBrand Lambda.fuel

oracleMachineScheme : Scheme PATask ℕ
oracleMachineScheme = mkScheme QuantumOracleProcess QuantumOracle.compileBrand QuantumOracle.fuel

quantumCircuitMachineScheme : Scheme PATask ℕ
quantumCircuitMachineScheme =
  mkScheme QuantumCircuitProcess QuantumCircuit.compileBrand QuantumCircuit.fuel

-- ============================================================================
-- Circuit families (uniform-by-bound)
--
-- Circuits become genuinely comparable to unbounded machine paradigms once they
-- are presented as families indexed by a resource bound. Here we index by a
-- step budget `k`, and compile a basis-state circuit that exposes the
-- observable result of running a chosen source for `k` steps.
-- ============================================================================

record Bounded (A : Set) : Set where
  constructor mkBounded
  field
    steps : ℕ
    input : A

open Bounded public

quantumCircuitFamilyChoice : Cat.Choice (Bounded PATask) QuantumCircuitProcess
quantumCircuitFamilyChoice =
  mkChoice QuantumCircuitProcess
    (λ bt → QuantumCircuit.compileFamilyFromMinsky (steps bt) (input bt))
    (λ _ → zero)

quantumCircuitFamilyScheme : Scheme (Bounded PATask) ℕ
quantumCircuitFamilyScheme =
  Cat.schemeFromChoice QuantumCircuitProcess quantumCircuitFamilyChoice

quantumCircuitFamily-run
  : ∀ bt → Sch.run quantumCircuitFamilyScheme bt ≡ observe (simulate (steps bt) (Minsky.compile (input bt)))
quantumCircuitFamily-run bt =
  -- `QuantumCircuitProcess.decode` observes via `UQC`, and the family compiler
  -- is defined to match `observe (simulate k (Minsky.compile t))`.
  QuantumCircuit.observe-familyFromU (steps bt) (Minsky.compile (input bt))

-- Process morphisms into the universal semantic center.

Minsky→U : Cat.ProcessHom MinskyProcess UProcess
Minsky→U =
  record
    { map        = UM
    ; mono       = λ {refl → refl}
    ; step-comm  = λ _ → refl
    ; norm-comm  = λ _ → refl
    ; decode-comm = λ _ → refl
    }

Minsky→UCost : Cat.ProcessHomCost MinskyProcess UProcess
Minsky→UCost =
  record
    { hom = Minsky→U
    ; Q-comm = refl
    ; stepCost-comm = λ _ → refl
    }

Ethereum→U : Cat.ProcessHom EthereumProcess UProcess
Ethereum→U =
  record
    { map        = UE
    ; mono       = λ {refl → refl}
    ; step-comm  = λ _ → refl
    ; norm-comm  = λ _ → refl
    ; decode-comm = λ _ → refl
    }

Ethereum→UCost : Cat.ProcessHomCost EthereumProcess UProcess
Ethereum→UCost =
  record
    { hom = Ethereum→U
    ; Q-comm = refl
    ; stepCost-comm = λ _ → refl
    }

Lambda→U : Cat.ProcessHom LambdaProcess UProcess
Lambda→U =
  record
    { map        = UL
    ; mono       = λ {refl → refl}
    ; step-comm  = λ _ → refl
    ; norm-comm  = λ _ → refl
    ; decode-comm = λ _ → refl
    }

Lambda→UCost : Cat.ProcessHomCost LambdaProcess UProcess
Lambda→UCost =
  record
    { hom = Lambda→U
    ; Q-comm = refl
    ; stepCost-comm = λ _ → refl
    }

Oracle→U : Cat.ProcessHom QuantumOracleProcess UProcess
Oracle→U =
  record
    { map        = UQ
    ; mono       = λ {refl → refl}
    ; step-comm  = λ _ → refl
    ; norm-comm  = λ _ → refl
    ; decode-comm = λ _ → refl
    }

Oracle→UCost : Cat.ProcessHomCost QuantumOracleProcess UProcess
Oracle→UCost =
  record
    { hom = Oracle→U
    ; Q-comm = refl
    ; stepCost-comm = λ _ → refl
    }

Circuit→U : Cat.ProcessHom QuantumCircuitProcess UProcess
Circuit→U =
  record
    { map        = UQC
    ; mono       = λ {refl → refl}
    ; step-comm  = λ _ → refl
    ; norm-comm  = λ _ → refl
    ; decode-comm = λ _ → refl
    }

Circuit→UCost : Cat.ProcessHomCost QuantumCircuitProcess UProcess
Circuit→UCost =
  record
    { hom = Circuit→U
    ; Q-comm = refl
    ; stepCost-comm = λ _ → refl
    }
