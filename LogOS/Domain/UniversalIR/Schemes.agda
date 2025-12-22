{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Schemes where

open import LogOS.Prelude
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)

open import LogOS.Adapters.QNat2 using (QNat2)
open import LogOS.Adapters.QNat2 as Q2 using (scaleOps; steps-budget-τ)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Minimal.ScaleOps using (ScaleOps)
open import LogOS.Computation.Scheme using (Scheme; Closure)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Domain.UniversalIR.Core
  using
    ( UCode; UM; UL; UE; UQ; UQC
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
open import LogOS.Domain.UniversalIR.IR using (lowerToIR; observe; lowerToIR-idem)
open import LogOS.Domain.UniversalIR.Task using (PATask)
open import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
open import LogOS.Domain.UniversalIR.Languages.Lambda as Lambda
open import LogOS.Domain.UniversalIR.Languages.Ethereum as Ethereum
open import LogOS.Domain.UniversalIR.Languages.QuantumOracle as QuantumOracle
open import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as QuantumCircuit

-- A simple numeric adapter: costs live in ℕ with the preorder ≤ and monoid +.

QSteps = QNat2

open QAdapter QSteps using (τ)

OpsSteps : ScaleOps QSteps
OpsSteps = Q2.scaleOps

-- Cost helpers (unitary/measurement split)

u₁ : ℕ → (ℕ × ℕ)
u₁ n = (n , zero)

m₁ : ℕ → (ℕ × ℕ)
m₁ n = (zero , n)

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
  { normalize  = λ u → u
  ; mono       = λ {u} {v} eq → eq
  ; infl       = λ _ → refl
  ; idemp-lax  = λ _ → refl
  }

observeU : UCode → ℕ
observeU = observe

-- A non-trivial quantale-cost profile (e.g. “gas”) for the universal carrier.
-- These weights are intentionally simple and purely structural: they show how
-- the quantale algebra composes costs across heterogeneous machine steps.

costMInstr : MInstr → ℕ
costMInstr HALT       = zero
costMInstr (INC _ _)  = suc zero
costMInstr (DECJZ _ _ _) = suc zero

stepCostM : MinskyCode → (ℕ × ℕ)
stepCostM m = u₁ (costMInstr (lookupDefault HALT (MinskyCode.prog m) (MinskyCode.pc m)))

gas : EInstr → ℕ
gas STOP      = suc zero
gas (PUSH _)  = suc zero
gas POP       = suc zero
gas ADD       = suc zero
gas MUL       = suc (suc zero)
gas SUB       = suc zero
gas DUP       = suc zero
gas SWAP      = suc zero
gas JUMP      = suc (suc zero)
gas JUMPI     = suc (suc zero)
gas MLOAD     = suc (suc (suc zero))
gas MSTORE    = suc (suc (suc zero))

stepCostE : EVMCode → (ℕ × ℕ)
stepCostE e = u₁ (gas (lookupDefault STOP (EVMCode.code e) (EVMCode.pc e)))

-- Quantum costs: measure dominates the nonunitary axis.
costQInstr : QInstr → (ℕ × ℕ)
costQInstr QHALT = u₁ zero
costQInstr (QINC _ _) = u₁ (suc zero)
costQInstr (QDECJZ _ _ _) = u₁ (suc zero)
costQInstr (MEASURE _ _ _) = m₁ (suc zero)

stepCostQ : QuantumCode → (ℕ × ℕ)
stepCostQ q = costQInstr (lookupDefault QHALT (QuantumCode.prog q) (QuantumCode.pc q))

costQCInstr : QCInstr → (ℕ × ℕ)
costQCInstr QCHALT = u₁ zero
costQCInstr QNOP = u₁ (suc zero)
costQCInstr (QX _) = u₁ (suc zero)
costQCInstr (QCNOT _ _) = u₁ (suc zero)
costQCInstr (QTOFF _ _ _) = u₁ (suc (suc zero))
costQCInstr (QMEASURE _ _ _) = m₁ (suc zero)

stepCostQC : QuantumCircuitCode → (ℕ × ℕ)
stepCostQC q = costQCInstr (lookupDefault QCHALT (QuantumCircuitCode.prog q) (QuantumCircuitCode.pc q))

stepCostᵁ : UCode → (ℕ × ℕ)
stepCostᵁ (UM m)  = stepCostM m
stepCostᵁ (UL _)  = u₁ (suc zero)
stepCostᵁ (UE e)  = stepCostE e
stepCostᵁ (UQ q)  = stepCostQ q
stepCostᵁ (UQC q) = stepCostQC q

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

-- Scale-indexed execution (machines as schemes):
-- running within a grade `g` means iterating for `steps (budget g)` steps.
run≤ᵁ : Cat.Process.Scale UProcess → UCode → UCode
run≤ᵁ = Cat.run≤ UProcess OpsSteps

-- The original `Sch.run` for each scheme uses a chosen `fuel : Input → ℕ`.
-- Under `QNat2.scaleOps`, `fuel` is exactly the step budget induced by the
-- grade `τ fuel` (second axis is measurement-only).
fuelGrade : (fuel : PATask → ℕ) → PATask → Cat.Process.Scale UProcess
fuelGrade fuel t = τ (fuel t)

minskyChoice : Cat.Choice PATask UProcess
minskyChoice = record { compile = Minsky.compile ; fuel = Minsky.fuel }

lambdaChoice : Cat.Choice PATask UProcess
lambdaChoice = record { compile = Lambda.compile ; fuel = Lambda.fuel }

ethereumChoice : Cat.Choice PATask UProcess
ethereumChoice = record { compile = Ethereum.compile ; fuel = Ethereum.fuel }

oracleChoice : Cat.Choice PATask UProcess
oracleChoice = record { compile = QuantumOracle.compile ; fuel = QuantumOracle.fuel }

quantumCircuitChoice : Cat.Choice PATask UProcess
quantumCircuitChoice = record { compile = QuantumCircuit.compile ; fuel = QuantumCircuit.fuel }

-- Five concrete “representation schemes” for the same PATask meaning.
-- (Same process, different choices.)

minskyScheme : Scheme PATask ℕ
minskyScheme = Cat.schemeFromChoice UProcess minskyChoice

lambdaScheme : Scheme PATask ℕ
lambdaScheme = Cat.schemeFromChoice UProcess lambdaChoice

ethereumScheme : Scheme PATask ℕ
ethereumScheme = Cat.schemeFromChoice UProcess ethereumChoice

oracleScheme : Scheme PATask ℕ
oracleScheme = Cat.schemeFromChoice UProcess oracleChoice

quantumCircuitScheme : Scheme PATask ℕ
quantumCircuitScheme = Cat.schemeFromChoice UProcess quantumCircuitChoice

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
-- as `run≤-*` at grade `τ (fuel t)`.
run≤-fuel≡run-minsky : ∀ t → run≤-minsky (fuelGrade Minsky.fuel t) t ≡ Sch.run minskyScheme t
run≤-fuel≡run-minsky t =
  cong (λ k → Sch.decode minskyScheme (Sch.normalize minskyScheme (Sch.exec minskyScheme k t)))
       (sym (Q2.steps-budget-τ (Minsky.fuel t)))

run≤-fuel≡run-lambda : ∀ t → run≤-lambda (fuelGrade Lambda.fuel t) t ≡ Sch.run lambdaScheme t
run≤-fuel≡run-lambda t =
  cong (λ k → Sch.decode lambdaScheme (Sch.normalize lambdaScheme (Sch.exec lambdaScheme k t)))
       (sym (Q2.steps-budget-τ (Lambda.fuel t)))

run≤-fuel≡run-ethereum : ∀ t → run≤-ethereum (fuelGrade Ethereum.fuel t) t ≡ Sch.run ethereumScheme t
run≤-fuel≡run-ethereum t =
  cong (λ k → Sch.decode ethereumScheme (Sch.normalize ethereumScheme (Sch.exec ethereumScheme k t)))
       (sym (Q2.steps-budget-τ (Ethereum.fuel t)))

run≤-fuel≡run-oracle : ∀ t → run≤-oracle (fuelGrade QuantumOracle.fuel t) t ≡ Sch.run oracleScheme t
run≤-fuel≡run-oracle t =
  cong (λ k → Sch.decode oracleScheme (Sch.normalize oracleScheme (Sch.exec oracleScheme k t)))
       (sym (Q2.steps-budget-τ (QuantumOracle.fuel t)))

run≤-fuel≡run-quantumCircuit
  : ∀ t → run≤-quantumCircuit (fuelGrade QuantumCircuit.fuel t) t ≡ Sch.run quantumCircuitScheme t
run≤-fuel≡run-quantumCircuit t =
  cong (λ k → Sch.decode quantumCircuitScheme (Sch.normalize quantumCircuitScheme (Sch.exec quantumCircuitScheme k t)))
       (sym (Q2.steps-budget-τ (QuantumCircuit.fuel t)))

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
  { normalize  = λ c → c
  ; mono       = λ p → p
  ; infl       = λ _ → ConPoset.refl CP
  ; idemp-lax  = λ _ → ConPoset.refl CP
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

MinskyProcessWith : (MinskyCode → (ℕ × ℕ)) → Cat.Process ℕ
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
    ; stepCost = λ _ → u₁ (suc zero)
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

minskyMachineChoice : Cat.Choice PATask MinskyProcess
minskyMachineChoice = record { compile = Minsky.compileBrand ; fuel = Minsky.fuel }

ethereumMachineChoice : Cat.Choice PATask EthereumProcess
ethereumMachineChoice = record { compile = Ethereum.compileBrand ; fuel = Ethereum.fuel }

lambdaMachineChoice : Cat.Choice PATask LambdaProcess
lambdaMachineChoice = record { compile = Lambda.compileBrand ; fuel = Lambda.fuel }

oracleMachineChoice : Cat.Choice PATask QuantumOracleProcess
oracleMachineChoice = record { compile = QuantumOracle.compileBrand ; fuel = QuantumOracle.fuel }

quantumCircuitMachineChoice : Cat.Choice PATask QuantumCircuitProcess
quantumCircuitMachineChoice = record { compile = QuantumCircuit.compileBrand ; fuel = QuantumCircuit.fuel }

minskyMachineScheme : Scheme PATask ℕ
minskyMachineScheme = Cat.schemeFromChoice MinskyProcess minskyMachineChoice

ethereumMachineScheme : Scheme PATask ℕ
ethereumMachineScheme = Cat.schemeFromChoice EthereumProcess ethereumMachineChoice

lambdaMachineScheme : Scheme PATask ℕ
lambdaMachineScheme = Cat.schemeFromChoice LambdaProcess lambdaMachineChoice

oracleMachineScheme : Scheme PATask ℕ
oracleMachineScheme = Cat.schemeFromChoice QuantumOracleProcess oracleMachineChoice

quantumCircuitMachineScheme : Scheme PATask ℕ
quantumCircuitMachineScheme =
  Cat.schemeFromChoice QuantumCircuitProcess quantumCircuitMachineChoice

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
  record
    { compile = λ bt → QuantumCircuit.compileFamilyFromMinsky (steps bt) (input bt)
    ; fuel    = λ _ → zero
    }

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
