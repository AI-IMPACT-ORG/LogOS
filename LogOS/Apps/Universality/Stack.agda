{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Stack where

-- Stack that packages several universality adapters into one stack kernel.
-- The measured-budget theorem family downstream reads the same fuel index as a
-- critical cutpoint rather than a pack-local side condition.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.LT.ConPreorder using (≡→≈)
open import LogOS.LT.View using (View)
open import LogOS.Ports.CriticalParameter using (CriticalCut)
import LogOS.LT.Stack as LTStack
open import LogOS.LT.Hom using (KernelHom)
import LogOS.LT.Hom as Hom
open import LogOS.LT.Kernel using (Kernel)

import LogOS.Ports.Universality.Core as Core
import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Adapters.Universality.Lambda as Lambda
import LogOS.Adapters.Universality.EVM as EVM
import LogOS.Adapters.Universality.PreQuantum as PreQuantum
import LogOS.Adapters.Universality.PreQuantumCircuit as PreQuantumCircuit

data UniversalityAdapter : Set where
  fromMinsky fromLambda fromEVM fromPreQuantum fromPreQuantumCircuit : UniversalityAdapter

allAdapters : List UniversalityAdapter
allAdapters =
  fromMinsky ∷
  fromLambda ∷
  fromEVM ∷
  fromPreQuantum ∷
  fromPreQuantumCircuit ∷
  []

record AdapterDescriptor : Set₁ where
  field
    Code : Set
    fuelAdapter : Core.FuelAdapter Code

open AdapterDescriptor public

adapterDescriptor : UniversalityAdapter → AdapterDescriptor
adapterDescriptor fromMinsky =
  record
    { Code = Minsky.MinskyCode
    ; fuelAdapter = Minsky.minskyFuelAdapter
    }
adapterDescriptor fromLambda =
  record
    { Code = Lambda.LambdaCode
    ; fuelAdapter = Lambda.lambdaFuelAdapter
    }
adapterDescriptor fromEVM =
  record
    { Code = EVM.EVMCode
    ; fuelAdapter = EVM.evmFuelAdapter
    }
adapterDescriptor fromPreQuantum =
  record
    { Code = PreQuantum.PreQuantumCode
    ; fuelAdapter = PreQuantum.preQuantumFuelAdapter
    }
adapterDescriptor fromPreQuantumCircuit =
  record
    { Code = PreQuantumCircuit.PreQuantumCircuitCode
    ; fuelAdapter = PreQuantumCircuit.preQuantumCircuitFuelAdapter
    }

adapterFuelAdapter : (adapter : UniversalityAdapter) → Core.FuelAdapter (Code (adapterDescriptor adapter))
adapterFuelAdapter adapter = fuelAdapter (adapterDescriptor adapter)

UniversalityAdapterCode : UniversalityAdapter → Set
UniversalityAdapterCode adapter = Code (adapterDescriptor adapter)

adapterCodeBoundary : ∀ adapter → UniversalityAdapterCode adapter → ℕ
adapterCodeBoundary adapter = Core.FuelAdapter.fuel (adapterFuelAdapter adapter)

adapterFuelBoundary : ∀ adapter → UniversalityAdapterCode adapter → ℕ
adapterFuelBoundary = adapterCodeBoundary

adapterFuel : ∀ adapter → UniversalityAdapterCode adapter → ℕ
adapterFuel = adapterFuelBoundary

adapterOperationView : ∀ adapter → View (UniversalityAdapterCode adapter) Core.universalBoundary
adapterOperationView adapter = record { μ = adapterCodeBoundary adapter }

adapterObservation : ∀ adapter → View (UniversalityAdapterCode adapter) Core.universalBoundary
adapterObservation = adapterOperationView

universalityStack : LTStack.Stack {ℓB = lzero} {ℓRel = lzero} {ℓOp = lzero} {ℓCode = lzero}
universalityStack =
  record
    { bnd = Core.universalBoundary
    ; Op = UniversalityAdapter
    ; Code = UniversalityAdapterCode
    ; op = adapterOperationView
    }

universalAdapterKernel : Kernel lzero lzero lzero
universalAdapterKernel = LTStack.stackKernel universalityStack

adapterKernel : (a : UniversalityAdapter) → Kernel lzero lzero lzero
adapterKernel = LTStack.opKernel universalityStack

adapterKernelHom
  : (a : UniversalityAdapter)
  → KernelHom (LTStack.opKernel universalityStack a) Core.universalKernel
adapterKernelHom a = Core.mkFuelToUniversal (adapterFuelAdapter a)

adapterCriticalBudget
  : (a : UniversalityAdapter)
  → (γ : UniversalityAdapterCode a)
  → CriticalCut
      Core.universalBoundary
      (λ budget → Core.BudgetEnough (adapterCodeBoundary a γ) budget)
adapterCriticalBudget a γ =
  Core.criticalBudget (adapterCodeBoundary a γ)

adapterMapCode-active
  : (a : UniversalityAdapter)
  → (γ : UniversalityAdapterCode a)
  → Hom.mapCode (adapterKernelHom a) γ
    ≡ Core.active (adapterCodeBoundary a γ)
adapterMapCode-active a γ = refl

adapterMapCode-observation
  : (a : UniversalityAdapter)
  → (γ : UniversalityAdapterCode a)
  → Core.universalObservation (Hom.mapCode (adapterKernelHom a) γ)
    ≡ adapterCodeBoundary a γ
adapterMapCode-observation a γ =
  cong Core.universalObservation (adapterMapCode-active a γ)

adapterView-observation
  : (a : UniversalityAdapter)
  → (γ : UniversalityAdapterCode a)
  → View.μ (LTStack.op universalityStack a) γ
    ≡ adapterCodeBoundary a γ
adapterView-observation a γ = refl

stackHomToUniversal : LTStack.StackMap universalityStack Core.universalKernel
stackHomToUniversal =
  record
    { map∂ = λ observationValue → observationValue
    ; map∂-mono = λ h → h
    ; mapCode = λ a γ → Hom.mapCode (adapterKernelHom a) γ
    ; decode-mapCode =
        λ a γ →
          ≡→≈
            {CP = Core.universalBoundary}
            (trans
              (adapterMapCode-observation a γ)
              (sym (adapterView-observation a γ)))
    }

stackToUniversal : KernelHom universalAdapterKernel Core.universalKernel
stackToUniversal = LTStack.toKernelHom stackHomToUniversal
