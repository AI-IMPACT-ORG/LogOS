{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.PhysicsClassesWCostGuardsGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude using (Σ; _,_; _×_; proj₁; proj₂)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.API.Kernel.Graded
open import LogOS.Complexity.Poly using (PolyPred)
import LogOS.Complexity.PhysicsClassesWGraded as PCW
import LogOS.Complexity.PolyGrade as PG
import LogOS.Complexity.LanguageWitnessW as LWW

-- Cost-guard refinement of the grade-native physical classes:
-- forbid degenerate “free” costs by demanding minimum input/witness grades.

module For {ℓI ℓW ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_)

  module Base = PCW.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  open Base public using (Language)

  record PhysDeciderCostGuards (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      PD : Base.PhysDecider L
      size≤cost : ∀ x → _≤g_ (gradeBound (size x)) (Base.PhysDecider.cost PD x)

  PhysPCostGuards : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  PhysPCostGuards L = Σ (PhysDeciderCostGuards L) (λ _ → ⊤ {ℓ = lzero})

  record PhysWitnessWCostGuards (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      PW : Base.PhysWitnessW L
      wsize≤checkCost
        : ∀ x w →
          _≤g_
            (gradeBound (LWW.WitnessSystemW.wsize (Base.PhysWitnessW.WS PW) w))
            (Base.PhysWitnessW.checkCost PW x w)

  PhysNPwCostGuards : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ)))
  PhysNPwCostGuards L = Σ (PhysWitnessWCostGuards L) (λ _ → ⊤ {ℓ = lzero})

  -- Forgetful maps back to the underlying classes.
  forgetP : ∀ {L} → PhysPCostGuards L → Base.PhysP L
  forgetP (pd , _) = PhysDeciderCostGuards.PD pd , tt

  forgetNPw : ∀ {L} → PhysNPwCostGuards L → Base.PhysNPw L
  forgetNPw (pw , _) = PhysWitnessWCostGuards.PW pw , tt

  notPhysPCostGuards : ∀ {L} → ¬ (Base.PhysP L) → ¬ (PhysPCostGuards L)
  notPhysPCostGuards notP ex = notP (forgetP ex)

-- Kernel-native boundedness surface (TruthRoute-based).
-- Mirrors the cost-guard names as aliases of the kernel route.

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

  module Base = PCW.Kernel K Input Size DetRun VerRun VerRunWith IsPoly gradeBound WSize

  open Base public using (Con; PhysP; PhysTotalNPw; SuperPolyHardness; notPhysP)

  PhysPCostGuards = PhysP
  PhysTotalNPwCostGuards = PhysTotalNPw
  notPhysPCostGuards = notPhysP

-- Grade-native kernel route (TruthRoute_Grade_Only-based).

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
  (PGG : PG.PolyPredG (QAdapter.Scale Q))
  (Pℕ : PolyPred)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module Base = PCW.KernelG K Input Size DetRun VerRun VerRunWith PGG Pℕ WSize

  open Base public using (Con; PhysP; PhysTotalNPw; SuperPolyHardness; notPhysP)

  PhysPCostGuards = PhysP
  PhysTotalNPwCostGuards = PhysTotalNPw
  notPhysPCostGuards = notPhysP
