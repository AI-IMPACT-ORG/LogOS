{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Agreement.Universal where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_; ≈-sym; ≡→≈; refl⊑)
open import LogOS.Syntax.Prop using (_↔_; intro; to; from)
open import LogOS.Ports.CriticalParameter using (CriticalCut; SharpCut)
import LogOS.LT.Hom as Hom

import LogOS.Ports.Universality.Core as Core
import LogOS.Apps.Universality.Stack as Stack

private
  module R = LogOS.Prelude.RefinementKit.Reasoning Core.universalBoundary
  open R using (begin≈_; _≈⟨_⟩_; _∎≈; begin⊑_; _⊑⟨_⟩_; _∎⊑)

universalFromAdapter
  : (a : Stack.UniversalityAdapter)
  → ∀ budgetCode
  → ∀ sourceCode
  → _≈_ Core.universalBoundary
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode (Hom.mapCode (Stack.adapterKernelHom a) sourceCode)))
      (Core.universalFuelAfter budgetCode (Core.active (Stack.adapterCodeBoundary a sourceCode)))
universalFromAdapter a budgetCode sourceCode =
  ≡→≈
    {CP = Core.universalBoundary}
    (trans
      (Core.runUniversalWithin-observation budgetCode (Hom.mapCode (Stack.adapterKernelHom a) sourceCode))
      (cong (Core.universalFuelAfter budgetCode) (Stack.adapterMapCode-active a sourceCode)))

record MeasuredEncoding {ℓA : Level}
  (A : Set ℓA)
  (measure : A → ℕ)
  (a : Stack.UniversalityAdapter)
  : Set ℓA where
  field
    encode : A → Stack.UniversalityAdapterCode a
    fuel-law : ∀ source → Stack.adapterCodeBoundary a (encode source) ≡ measure source

open MeasuredEncoding public

mkMeasuredEncoding
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    {a : Stack.UniversalityAdapter}
  → (encode : A → Stack.UniversalityAdapterCode a)
  → (fuel-law : ∀ source → Stack.adapterCodeBoundary a (encode source) ≡ measure source)
  → MeasuredEncoding A measure a
mkMeasuredEncoding encode fuel-law =
  record
    { encode = encode
    ; fuel-law = fuel-law
    }

MeasuredBudgetEnough
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
  → MeasuredEncoding A measure a
  → A
  → ℕ
  → Set
MeasuredBudgetEnough {measure = measure} a E source budgetCode =
  _⊑_ Core.universalBoundary (measure source) budgetCode

measuredCriticalBudget
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
  → (E : MeasuredEncoding A measure a)
  → (source : A)
  → CriticalCut
      Core.universalBoundary
      (MeasuredBudgetEnough a E source)
measuredCriticalBudget {measure = measure} a E source =
  Core.criticalBudget (measure source)

MeasuredObservationExhausted
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
  → MeasuredEncoding A measure a
  → A
  → ℕ
  → Set
MeasuredObservationExhausted a E source budgetCode =
  _⊑_ Core.universalBoundary
    (Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom a) (encode E source))))
    zero

measuredObservationExhausted↔Enough
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
  → ∀ budgetCode (source : A)
  → MeasuredObservationExhausted a E source budgetCode
      ↔ MeasuredBudgetEnough a E source budgetCode
measuredObservationExhausted↔Enough {measure = measure} a E budgetCode source =
  intro exhausted→enough enough→exhausted
  where
    observation≈fuel
      : _≈_ Core.universalBoundary
          (Core.universalObservation
            (Core.runUniversalWithin budgetCode
              (Hom.mapCode (Stack.adapterKernelHom a) (encode E source))))
          (Core.universalFuelAfter budgetCode (Core.active (measure source)))
    observation≈fuel =
      begin≈
        Core.universalObservation
          (Core.runUniversalWithin budgetCode
            (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
          ≈⟨ universalFromAdapter a budgetCode (encode E source) ⟩
        Core.universalFuelAfter budgetCode
          (Core.active (Stack.adapterCodeBoundary a (encode E source)))
          ≈⟨ ≡→≈
                {CP = Core.universalBoundary}
                (cong (Core.universalFuelAfter budgetCode) (cong Core.active (fuel-law E source))) ⟩
        Core.universalFuelAfter budgetCode (Core.active (measure source))
          ∎≈

    exhausted→enough
      : MeasuredObservationExhausted a E source budgetCode
      → MeasuredBudgetEnough a E source budgetCode
    exhausted→enough exhausted =
      to (Core.fuelExhausted↔budgetEnough (measure source) budgetCode)
        (begin⊑
          Core.universalFuelAfter budgetCode (Core.active (measure source))
            ⊑⟨ snd observation≈fuel ⟩
          Core.universalObservation
            (Core.runUniversalWithin budgetCode
              (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
            ⊑⟨ exhausted ⟩
          zero ∎⊑)

    enough→exhausted
      : MeasuredBudgetEnough a E source budgetCode
      → MeasuredObservationExhausted a E source budgetCode
    enough→exhausted enough =
      begin⊑
        Core.universalObservation
          (Core.runUniversalWithin budgetCode
            (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
          ⊑⟨ fst observation≈fuel ⟩
        Core.universalFuelAfter budgetCode (Core.active (measure source))
          ⊑⟨ from (Core.fuelExhausted↔budgetEnough (measure source) budgetCode) enough ⟩
        zero ∎⊑

MeasuredObservation
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
  → MeasuredEncoding A measure a
  → Set ℓA
MeasuredObservation {A = A} {measure = measure} a E =
  ∀ budgetCode (source : A)
  → _≈_ Core.universalBoundary
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode
          (Hom.mapCode (Stack.adapterKernelHom a) (encode E source))))
      (Core.universalFuelAfter budgetCode (Core.active (measure source)))

measuredObservation
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
  → MeasuredObservation a E
measuredObservation {measure = measure} a E budgetCode source =
  begin≈
    Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
      ≈⟨ universalFromAdapter a budgetCode (encode E source) ⟩
    Core.universalFuelAfter budgetCode
      (Core.active (Stack.adapterCodeBoundary a (encode E source)))
      ≈⟨ ≡→≈
            {CP = Core.universalBoundary}
            (cong (Core.universalFuelAfter budgetCode) (cong Core.active (fuel-law E source))) ⟩
    Core.universalFuelAfter budgetCode (Core.active (measure source))
      ∎≈

measuredObservationZeroAboveCritical
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
  → ∀ budgetCode (source : A)
  → MeasuredBudgetEnough a E source budgetCode
  → _≈_ Core.universalBoundary
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode
          (Hom.mapCode (Stack.adapterKernelHom a) (encode E source))))
      zero
measuredObservationZeroAboveCritical {measure = measure} a E budgetCode source enough =
  begin≈
    Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
      ≈⟨ measuredObservation a E budgetCode source ⟩
    Core.universalFuelAfter budgetCode (Core.active (measure source))
      ≈⟨ ≡→≈
            {CP = Core.universalBoundary}
            (Core.universalFuelAfter-zeroWhenEnough (measure source) budgetCode enough) ⟩
    zero ∎≈

MeasuredAgreementExhausted
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
  → MeasuredEncoding A measure a
  → MeasuredEncoding A measure b
  → A
  → ℕ
  → Set
MeasuredAgreementExhausted a b E F source budgetCode =
  MeasuredObservationExhausted a E source budgetCode
  ×
  MeasuredObservationExhausted b F source budgetCode

measuredAgreementExhausted↔Enough
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
    (F : MeasuredEncoding A measure b)
  → ∀ budgetCode (source : A)
  → MeasuredAgreementExhausted a b E F source budgetCode
      ↔ MeasuredBudgetEnough a E source budgetCode
measuredAgreementExhausted↔Enough a b E F budgetCode source =
  intro exhausted→enough enough→exhausted
  where
    exhausted→enough
      : MeasuredAgreementExhausted a b E F source budgetCode
      → MeasuredBudgetEnough a E source budgetCode
    exhausted→enough (aExhausted , _) =
      to (measuredObservationExhausted↔Enough a E budgetCode source) aExhausted

    enough→exhausted
      : MeasuredBudgetEnough a E source budgetCode
      → MeasuredAgreementExhausted a b E F source budgetCode
    enough→exhausted enough =
      ( from (measuredObservationExhausted↔Enough a E budgetCode source) enough
      , from (measuredObservationExhausted↔Enough b F budgetCode source) enough
      )

measuredAgreementCriticalCut
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
    (F : MeasuredEncoding A measure b)
    (source : A)
  → CriticalCut
      Core.universalBoundary
      (MeasuredAgreementExhausted a b E F source)
measuredAgreementCriticalCut a b E F source =
  record
    { good-mono = λ {t} {u} t≤u exhaustedAtT →
        from (measuredAgreementExhausted↔Enough a b E F u source)
          (begin⊑
            CriticalCut.Λ (measuredCriticalBudget a E source)
              ⊑⟨ to (measuredAgreementExhausted↔Enough a b E F t source) exhaustedAtT ⟩
            t ⊑⟨ t≤u ⟩
            u ∎⊑)
    ; Λ = CriticalCut.Λ (measuredCriticalBudget a E source)
    ; GoodAbove = λ {t} enough →
        from (measuredAgreementExhausted↔Enough a b E F t source) enough
    ; least = λ {cut} cutGood →
        to
          (measuredAgreementExhausted↔Enough a b E F cut source)
          (cutGood (ConPreorder.refl Core.universalBoundary))
    }

measuredAgreementSharpCut
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
    (F : MeasuredEncoding A measure b)
    (source : A)
  → SharpCut
      Core.universalBoundary
      (MeasuredAgreementExhausted a b E F source)
measuredAgreementSharpCut a b E F source =
  record
    { base = measuredAgreementCriticalCut a b E F source
    ; belowFails = λ {budgetCode} (_ , budget⋠Λ) exhaustedAtBudget →
        budget⋠Λ
          (to
            (measuredAgreementExhausted↔Enough a b E F budgetCode source)
            exhaustedAtBudget)
    }

MeasuredAgreement
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
  → MeasuredEncoding A measure a
  → MeasuredEncoding A measure b
  → Set ℓA
MeasuredAgreement {A = A} a b E F =
  ∀ budgetCode (source : A)
  → _≈_ Core.universalBoundary
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode
          (Hom.mapCode (Stack.adapterKernelHom a) (encode E source))))
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode
          (Hom.mapCode (Stack.adapterKernelHom b) (encode F source))))

measuredAgreement
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
    (F : MeasuredEncoding A measure b)
  → MeasuredAgreement a b E F
measuredAgreement {measure = measure} a b E F budgetCode source =
  begin≈
    Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
      ≈⟨ measuredObservation a E budgetCode source ⟩
    Core.universalFuelAfter budgetCode (Core.active (measure source))
      ≈⟨ ≈-sym {CP = Core.universalBoundary} (measuredObservation b F budgetCode source) ⟩
    Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom b) (encode F source)))
      ∎≈

measuredAgreementAboveCritical
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a b : Stack.UniversalityAdapter)
    (E : MeasuredEncoding A measure a)
    (F : MeasuredEncoding A measure b)
  → ∀ budgetCode (source : A)
  → MeasuredBudgetEnough a E source budgetCode
  → _≈_ Core.universalBoundary
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode
          (Hom.mapCode (Stack.adapterKernelHom a) (encode E source))))
      (Core.universalObservation
        (Core.runUniversalWithin budgetCode
          (Hom.mapCode (Stack.adapterKernelHom b) (encode F source))))
measuredAgreementAboveCritical a b E F budgetCode source enough =
  begin≈
    Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom a) (encode E source)))
      ≈⟨ measuredObservationZeroAboveCritical a E budgetCode source enough ⟩
    zero
      ≈⟨ ≈-sym {CP = Core.universalBoundary}
            (measuredObservationZeroAboveCritical b F budgetCode source enough) ⟩
    Core.universalObservation
      (Core.runUniversalWithin budgetCode
        (Hom.mapCode (Stack.adapterKernelHom b) (encode F source)))
      ∎≈

record MeasuredEncodings {ℓA : Level}
  (A : Set ℓA)
  (measure : A → ℕ)
  : Set ℓA where
  field
    minsky : MeasuredEncoding A measure Stack.fromMinsky
    lambda : MeasuredEncoding A measure Stack.fromLambda
    evm : MeasuredEncoding A measure Stack.fromEVM
    preQuantum : MeasuredEncoding A measure Stack.fromPreQuantum
    preQuantumCircuit : MeasuredEncoding A measure Stack.fromPreQuantumCircuit

open MeasuredEncodings public

mkMeasuredEncodings
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
  → MeasuredEncoding A measure Stack.fromMinsky
  → MeasuredEncoding A measure Stack.fromLambda
  → MeasuredEncoding A measure Stack.fromEVM
  → MeasuredEncoding A measure Stack.fromPreQuantum
  → MeasuredEncoding A measure Stack.fromPreQuantumCircuit
  → MeasuredEncodings A measure
mkMeasuredEncodings minsky lambda evm preQuantum preQuantumCircuit =
  record
    { minsky = minsky
    ; lambda = lambda
    ; evm = evm
    ; preQuantum = preQuantum
    ; preQuantumCircuit = preQuantumCircuit
    }

record ParadigmsAgreement {ℓA : Level}
  (A : Set ℓA)
  (measure : A → ℕ)
  (E : MeasuredEncodings A measure)
  : Set ℓA where
  field
    minsky≈lambda : MeasuredAgreement Stack.fromMinsky Stack.fromLambda (minsky E) (lambda E)
    lambda≈evm : MeasuredAgreement Stack.fromLambda Stack.fromEVM (lambda E) (evm E)
    evm≈preQuantum : MeasuredAgreement Stack.fromEVM Stack.fromPreQuantum (evm E) (preQuantum E)
    preQuantum≈preQuantumCircuit
      : MeasuredAgreement
          Stack.fromPreQuantum
          Stack.fromPreQuantumCircuit
          (preQuantum E)
          (preQuantumCircuit E)

open ParadigmsAgreement public

measuredParadigmsAgreement
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (E : MeasuredEncodings A measure)
  → ParadigmsAgreement A measure E
measuredParadigmsAgreement E =
  record
    { minsky≈lambda = measuredAgreement Stack.fromMinsky Stack.fromLambda (minsky E) (lambda E)
    ; lambda≈evm = measuredAgreement Stack.fromLambda Stack.fromEVM (lambda E) (evm E)
    ; evm≈preQuantum = measuredAgreement Stack.fromEVM Stack.fromPreQuantum (evm E) (preQuantum E)
    ; preQuantum≈preQuantumCircuit =
        measuredAgreement
          Stack.fromPreQuantum
          Stack.fromPreQuantumCircuit
          (preQuantum E)
          (preQuantumCircuit E)
    }

measuredAgreementCut
  : ∀ {ℓA : Level}
    {A : Set ℓA}
    {measure : A → ℕ}
    (a : Stack.UniversalityAdapter)
  → (E : MeasuredEncoding A measure a)
  → (source : A)
  → CriticalCut
      Core.universalBoundary
      (MeasuredBudgetEnough a E source)
measuredAgreementCut = measuredCriticalBudget
