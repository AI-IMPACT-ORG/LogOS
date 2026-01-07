{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PhysicsClassesWGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s) public

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded
open import LogOS.Domain.Complexity.Poly using (PolyPred)
open import LogOS.Domain.Complexity.LanguageWitness as LW
import LogOS.Domain.Complexity.LanguageWitnessW as LWW
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Domain.Complexity.PolyGrade as PG

-- Grade-native physical classes with witness size (NP-style).
-- Cost bounds live in the grade; polynomials remain ℕ-indexed.

module For {ℓI ℓW ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_)

  Language : Set (ℓI ⊔ lsuc ℓ)
  Language = Input → Set ℓ

  record PhysDecider (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      D : LW.DeciderI Input L
      cost : Input → Grade
      bound : ℕ → ℕ
      polyBound : PolyPred.isPoly Pℕ bound
      cost≤ : ∀ x → _≤g_ (cost x) (gradeBound (bound (size x)))

  -- Grade-bounded deciders (no ℕ-bound wrapper).
  record PhysDeciderG (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      D : LW.DeciderI Input L
      cost : Input → Grade
      boundG : ℕ → Grade
      cost≤ : ∀ x → _≤g_ (cost x) (boundG (size x))

  toPhysDeciderG : ∀ {L} → PhysDecider L → PhysDeciderG L
  toPhysDeciderG PD =
    record
      { D      = PhysDecider.D PD
      ; cost   = PhysDecider.cost PD
      ; boundG = λ n → gradeBound (PhysDecider.bound PD n)
      ; cost≤  = PhysDecider.cost≤ PD
      }

  PhysP : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  PhysP L = Σ (PhysDecider L) (λ _ → ⊤ {ℓ = lzero})

  PhysPG : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  PhysPG L = Σ (PhysDeciderG L) (λ _ → ⊤ {ℓ = lzero})

  -- NP with witness size (not finite-search NP).
  record PhysWitnessW (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      WS : LWW.WitnessSystemW {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} Input L
      checkCost : ∀ x → LWW.WitnessSystemW.W WS x → Grade
      checkBound : ℕ → ℕ
      polyCheck : PolyPred.isPoly Pℕ checkBound
      checkCost≤ : ∀ x w → _≤g_ (checkCost x w) (gradeBound (checkBound (size x)))

  -- Grade-bounded witness systems (no ℕ-bound wrapper).
  record PhysWitnessWG (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      WS : LWW.WitnessSystemW {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} Input L
      checkCost : ∀ x → LWW.WitnessSystemW.W WS x → Grade
      checkBoundG : ℕ → Grade
      checkCost≤ : ∀ x w → _≤g_ (checkCost x w) (checkBoundG (size x))

  toPhysWitnessWG : ∀ {L} → PhysWitnessW L → PhysWitnessWG L
  toPhysWitnessWG PW =
    record
      { WS          = PhysWitnessW.WS PW
      ; checkCost   = PhysWitnessW.checkCost PW
      ; checkBoundG = λ n → gradeBound (PhysWitnessW.checkBound PW n)
      ; checkCost≤  = PhysWitnessW.checkCost≤ PW
      }

  PhysNPw : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ)))
  PhysNPw L = Σ (PhysWitnessW L) (λ _ → ⊤ {ℓ = lzero})

  PhysNPwG : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ)))
  PhysNPwG L = Σ (PhysWitnessWG L) (λ _ → ⊤ {ℓ = lzero})

  record PhysSeparationW (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      inNPw : PhysNPw L
      detSuperPoly : ∀ (PD : PhysDecider L) →
        Σ Input (λ x → ¬ (PhysDecider.cost PD x ≤g gradeBound (PhysDecider.bound PD (size x))))

  record PhysSeparationWG (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      inNPwG : PhysNPwG L
      detSuperPolyG : ∀ (PD : PhysDeciderG L) →
        Σ Input (λ x → ¬ (PhysDeciderG.cost PD x ≤g PhysDeciderG.boundG PD (size x)))

  notPhysP
    : ∀ {L}
      → (∀ (PD : PhysDecider L) →
           Σ Input (λ x → ¬ (PhysDecider.cost PD x ≤g gradeBound (PhysDecider.bound PD (size x)))))
      → ¬ PhysP L
  notPhysP sp (pd , _) =
    let ex = sp pd in
    ⊥-elim (proj₂ ex (PhysDecider.cost≤ pd (proj₁ ex)))

  notPhysPG
    : ∀ {L}
      → (∀ (PD : PhysDeciderG L) →
           Σ Input (λ x → ¬ (PhysDeciderG.cost PD x ≤g PhysDeciderG.boundG PD (size x))))
      → ¬ PhysPG L
  notPhysPG sp (pd , _) =
    let ex = sp pd in
    ⊥-elim (proj₂ ex (PhysDeciderG.cost≤ pd (proj₁ ex)))

-- Kernel-native boundedness surface (TruthRoute-based).
-- Uses graded Flow bounds instead of raw cost comparisons.

module Kernel
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module R = TRG.ForNat K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module W = R.WithWitnessSize WSize

  Con : Set ℓ
  Con = R.Con

  PhysP : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓA)
  PhysP = R.DetPolyTimeBounded

  PhysNPw : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA)
  PhysNPw = W.PolyWitnessedTotalVerificationW

  SuperPolyHardness : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓA)
  SuperPolyHardness = R.SuperPolyHardness

  notPhysP : ∀ {ℓA} {Acc : Con → Set ℓA} → SuperPolyHardness Acc → ¬ PhysP Acc
  notPhysP {Acc = Acc} = R.noDetPolyTimeBounded {Acc = Acc}

-- Kernel-native boundedness surface (TruthRoute_Grade_Only-based).
-- Grade polynomials live in `PolyPredG`; witness bounds remain ℕ-polynomial.

module KernelG
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (PG : PG.PolyPredG (QAdapter.Scale Q))
  (Pℕ : PolyPred)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module R = TRG.For K Input Size DetRun VerRun VerRunWith
  module G = R.GradeBounded PG
  module W = G.WithWitnessSizeG (PolyPred.isPoly Pℕ) WSize

  Con : Set ℓ
  Con = R.Con

  PhysP : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
  PhysP = G.DetPolyTimeBoundedG

  PhysNPw : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
  PhysNPw = W.PolyWitnessedTotalVerificationWG

  SuperPolyHardness : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
  SuperPolyHardness = G.SuperPolyHardnessG

  notPhysP : ∀ {ℓA} {Acc : Con → Set ℓA} → SuperPolyHardness Acc → ¬ PhysP Acc
  notPhysP {Acc = Acc} = G.noDetPolyTimeBoundedG {Acc = Acc}
