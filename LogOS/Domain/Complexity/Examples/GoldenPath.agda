{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Examples.GoldenPath where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Hom

open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PolyGrade as PG
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PFI
import LogOS.Domain.Complexity.PhysToTruthRouteBridge as Bridge
import LogOS.Domain.Complexity.ClassicalPvsNP as CP
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TR

-- Golden path skeleton:
-- grade-native core (info-hardness) → grade-hom bridge → classical alignment at the end.

module Core
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (PGG : PG.PolyPredG (QAdapter.Scale Q))
  where

  module Route = PFI.For K Input Size DetRun VerRun VerRunWith PGG
  open Route public

module BridgeFromNat
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun₁ : Input → GradedKernel.Code K₁)
  (VerRun₁ : Input → GradedKernel.Code K₁)
  (VerRunWith₁ : Input → GradedKernel.Code K₁ → GradedKernel.Code K₁)
  (DetRun₂ : Input → GradedKernel.Code K₂)
  (VerRun₂ : Input → GradedKernel.Code K₂)
  (VerRunWith₂ : Input → GradedKernel.Code K₂ → GradedKernel.Code K₂)
  (Pℕ : PolyPred)
  (gradeBound₁ : ℕ → QAdapter.Scale Q₁)
  (gradeBound₂ : ℕ → QAdapter.Scale Q₂)
  (grade-coh : ∀ n →
     gradeBound₂ n ≡
       (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
        GH.map (gradeBound₁ n)))
  (det-map : ∀ x → GradedKernelHomWithGrade.mapCode h (DetRun₁ x) ≡ DetRun₂ x)
  (ver-map : ∀ x → GradedKernelHomWithGrade.mapCode h (VerRun₁ x) ≡ VerRun₂ x)
  (verw-map : ∀ x w → GradedKernelHomWithGrade.mapCode h (VerRunWith₁ x w)
                     ≡ VerRunWith₂ x (GradedKernelHomWithGrade.mapCode h w))
  where

  module Base =
    Bridge.ForGFromNat
      K₁ K₂ h hf Input Size
      DetRun₁ VerRun₁ VerRunWith₁
      DetRun₂ VerRun₂ VerRunWith₂
      Pℕ gradeBound₁ gradeBound₂ grade-coh
      det-map ver-map verw-map

  module WithBack
    (back : QAdapter.Scale Q₂ → QAdapter.Scale Q₁)
    (map-back : ∀ g₂ →
       (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
        GH.map (back g₂)) ≡ g₂)
    (poly-back
      : ∀ g₂ →
        PG.PolyPredG.isPolyG Base.PG₂.polyPredG g₂ →
        PG.PolyPredG.isPolyG Base.PG₁.polyPredG (λ n → back (g₂ n)))
    where

    open Base.WithBack back map-back poly-back public

module ClassicalAlignment
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (WSize : GradedKernel.Code K → ℕ)
  (Pℕ : PolyPred)
  where

  IsPoly : (ℕ → ℕ) → Set
  IsPoly = PolyPred.isPoly Pℕ

  module Rℕ = TR.ForNat K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module Wℕ = Rℕ.WithWitnessSize WSize

  module CS =
    CP.FromTruthRoute
      K Input Size DetRun VerRun VerRunWith
      IsPoly gradeBound WSize Pℕ (λ {p} pp → pp)

  module ForLanguage {ℓL : Level} (L : Rℕ.Language ℓL) where
    module L₀ = CS.ForLanguage {ℓL = ℓL} L

    toClassicalInP : Rℕ.InP {ℓL = ℓL} L → L₀.C.InP L
    toClassicalInP = L₀.fromInP

    toClassicalInNP : Wℕ.InNP {ℓL = ℓL} L → L₀.C.InNP L
    toClassicalInNP = L₀.fromInNP

-- -------------------------------------------------------------------------
-- Minsky-backed instantiation (previously in GoldenPathMinsky).
-- -------------------------------------------------------------------------

module Minsky (Pℕ : PolyPred) where
  open import Data.NatOrder using (_≤ℕ_; ≤ℕ-refl; z≤n; s≤s; weakenRight; trans≤ℕ)

  open import LogOS.Minimal.ScaleOps using (ScaleOps)
  import LogOS.Domain.Complexity.UniversalIRCM as UIR
  import LogOS.Domain.Complexity.PolyGrade as PG

  import LogOS.Computation.Scheme as Sch
  open import LogOS.Domain.UniversalIR.Core
    using (UCode; MinskyCode; HALT; INC; DECJZ; lookupDefault; prog; pc; stepM)
  import LogOS.Domain.UniversalIR.Schemes as Schemes
  import LogOS.Domain.UniversalIR.Examples.SchemeChoices as Choices
  import LogOS.Domain.UniversalIR.KernelRichG as KR

  -- Concrete scheme factorization (machines as schemes).
  module SchemeFactorization where
    open Schemes public using (minskyMachineScheme)
    open Choices public using (minskyFactorsThroughU; minskyCostFactorsThroughU)

  module For
    {Sig : LogOSSignature lzero}
    {Q : QAdapter lzero}
    (K : GradedKernel Sig Q)
    (Ops : ScaleOps Q)
    (toCodeK : UCode → GradedKernel.Code K)
    (fromCodeK : GradedKernel.Code K → UCode)
    (gradeBound : ℕ → QAdapter.Scale Q)
    where

    M : UIR.StandardCMᴵᴿ {ℓ = lzero}
    M = UIR.mkIRCM Pℕ UIR.minsky

    open UIR.StandardCMᴵᴿ M renaming
      ( Input  to Inputᵀ
      ; size   to sizeᵀ
      ; wsize  to wsizeᵀ
      )

    module UTR = UIR.TR K toCodeK fromCodeK gradeBound M
    module PGN = PG.FromNat Q Pℕ gradeBound

    module GPCore =
      Core
        K Inputᵀ sizeᵀ
        UTR.DetRun UTR.VerRun UTR.VerRunWith
        PGN.polyPredG

    open GPCore public

    WSize : GradedKernel.Code K → ℕ
    WSize w = wsizeᵀ (fromCodeK w)

    open ScaleOps Ops renaming (budget to budgetG; steps to stepsG)

    Budget : QAdapter.Scale Q → ℕ
    Budget g = stepsG (budgetG g)

    SizeBudget : Set
    SizeBudget = ∀ x → sizeᵀ x ≤ℕ Budget (gradeBound (sizeᵀ x))

    FuelBudget : Set
    FuelBudget = ∀ x → UIR.fuel UIR.minsky x ≤ℕ Budget (gradeBound (sizeᵀ x))

    costSteps : (ℕ × ℕ) → ℕ
    costSteps (n , _) = n

    stepCostM≤1 : ∀ m → costSteps (Schemes.stepCostM m) ≤ℕ suc zero
    stepCostM≤1 m with lookupDefault HALT (prog m) (pc m)
    ... | HALT = z≤n
    ... | INC _ _ = ≤ℕ-refl
    ... | DECJZ _ _ _ = ≤ℕ-refl

    ≤1+≤n→≤suc : ∀ {a b n} → a ≤ℕ suc zero → b ≤ℕ n → a + b ≤ℕ suc n
    ≤1+≤n→≤suc z≤n      b≤n = weakenRight b≤n
    ≤1+≤n→≤suc (s≤s z≤n) b≤n = s≤s b≤n

    costExec≤steps : ∀ n (m : MinskyCode) →
      costSteps (Sch.costExec Schemes.minskyMachineScheme n m) ≤ℕ n
    costExec≤steps zero    _ = z≤n
    costExec≤steps (suc n) m =
      ≤1+≤n→≤suc (stepCostM≤1 m) (costExec≤steps n (stepM m))

    cost≤fuel : ∀ x →
      costSteps (Sch.cost Schemes.minskyMachineScheme x) ≤ℕ UIR.fuel UIR.minsky x
    cost≤fuel x =
      costExec≤steps
        (UIR.fuel UIR.minsky x)
        (Sch.compile Schemes.minskyMachineScheme x)

    cost≤budget : FuelBudget → ∀ x →
      costSteps (Sch.cost Schemes.minskyMachineScheme x) ≤ℕ
      Budget (gradeBound (sizeᵀ x))
    cost≤budget fuel≤budget x =
      trans≤ℕ (cost≤fuel x) (fuel≤budget x)

    module Align =
      ClassicalAlignment
        K Inputᵀ sizeᵀ
        UTR.DetRun UTR.VerRun UTR.VerRunWith
        gradeBound WSize Pℕ

    open Align public

  -- Fully concrete instantiation: kernel code is UCode and decode is id.
  module Concrete where
    open KR
    open QAdapter Q using (τ)

    gradeBound : ℕ → QAdapter.Scale Q
    gradeBound n = τ n

    module Inst =
      For {Sig = KR.Sig} {Q = KR.Q}
        KR.GUKR
        KR.Ops
        (λ u → u)
        (λ u → u)
        gradeBound

    open Inst public

    size≤budget : Inst.SizeBudget
    size≤budget _ = ≤ℕ-refl
