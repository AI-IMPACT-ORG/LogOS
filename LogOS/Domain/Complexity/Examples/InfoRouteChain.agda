{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Examples.InfoRouteChain where

open import LogOS.Prelude

open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded

open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PolyGrade as PG
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Domain.Complexity.InfoBottleneckAdaptersG as IBG
import LogOS.Domain.Complexity.ObservabilityBudgetG as OB
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PFI
import LogOS.Domain.Complexity.ClassicalPvsNP as CP

-- End-to-end skeleton for the minimal info-theory route:
-- LOB → DetBottleneck → InfoHardness → PvsNPFromInfo.
-- This stays kernel-native and keeps classical alignment explicit (separate).

module For
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

  module R = TRG.For K Input Size DetRun VerRun VerRunWith
  module G = R.GradeBounded PGG

  module WithAcc {ℓA} (Acc : R.Con → Set ℓA) where
    module B = IBG.FromLOB Input Size Q (PG.PolyPredG.isPolyG PGG) (R.DetWithinAt Acc)
    module O = OB.For {ℓI = ℓI} {ℓ = ℓA} {ℓQ = ℓ} Input Size Q
    module P = PFI.For K Input Size DetRun VerRun VerRunWith PGG
    module A = P.WithAcc Acc

    -- Non-degeneracy guard for examples: ensure budgets can at least read input.
    record NonDegenerate (lob : O.LOB) (sizeGrade : ℕ → R.Grade)
      : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA)) where
      field
        size≤budget : ∀ x → Size x ≤ℕ O.LOB.budget lob (sizeGrade (Size x))

    detBottleneckFromLOB : O.LOB → B.DetRunAsQTimeG → A.DetBottleneck
    detBottleneckFromLOB lob dr = B.detBottleneck lob dr

    claimFromLOB
      : G.PolyWitnessedTotalVerificationG Acc
      → (lob : O.LOB)
      → (dr : B.DetRunAsQTimeG)
      → A.InfoHardness (detBottleneckFromLOB lob dr)
      → G.PvsNPClaimG Acc
    claimFromLOB np lob dr hard =
      A.Pack.claim
        (A.mkPack
          (record
            { NP-witnessG = np
            ; BtlG        = detBottleneckFromLOB lob dr
            ; hardG       = hard
            }))

    claimFromLOB-nondegenerate
      : G.PolyWitnessedTotalVerificationG Acc
      → (lob : O.LOB)
      → (sizeGrade : ℕ → R.Grade)
      → NonDegenerate lob sizeGrade
      → (dr : B.DetRunAsQTimeG)
      → A.InfoHardness (detBottleneckFromLOB lob dr)
      → G.PvsNPClaimG Acc × NonDegenerate lob sizeGrade
    claimFromLOB-nondegenerate np lob sizeGrade nd dr hard =
      claimFromLOB np lob dr hard , nd

  -- Literature alignment (separate surface): map TruthRoute P/NP to classical P/NP.
  module ClassicalAlignment
    {ℓP : Level}
    (IsPoly : (ℕ → ℕ) → Set ℓP)
    (gradeBound : ℕ → QAdapter.Scale Q)
    (WSize : GradedKernel.Code K → ℕ)
    (Pℕ : PolyPred)
    {ℓL : Level}
    (polyOk : ∀ {p : ℕ → ℕ} → IsPoly p → PolyPred.isPoly Pℕ p)
    where

    module Rℕ = TRG.ForNat K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
    module Wℕ = Rℕ.WithWitnessSize WSize

    module CS = CP.FromTruthRoute
      K Input Size DetRun VerRun VerRunWith IsPoly gradeBound WSize Pℕ polyOk

    module ForLanguage (L : Rℕ.Language ℓL) where
      module L₀ = CS.ForLanguage {ℓL = ℓL} L

      toClassicalInP : Rℕ.InP {ℓL = ℓL} L → L₀.C.InP L
      toClassicalInP = L₀.fromInP

      toClassicalInNP : Wℕ.InNP {ℓL = ℓL} L → L₀.C.InNP L
      toClassicalInNP = L₀.fromInNP

module ForFromNat
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
  (Pℕ : PolyPred)
  where

  module PGN = PG.FromNat Q Pℕ gradeBound
  module Core = For K Input Size DetRun VerRun VerRunWith PGN.polyPredG
  open Core public

-- -------------------------------------------------------------------------
-- UniversalIR instantiation (previously in InfoRouteChainIR).
-- -------------------------------------------------------------------------

module UniversalIR where
  open import LogOS.Domain.UniversalIR.Core using (UCode)
  import LogOS.Domain.Complexity.UniversalIRCM as UIR

  module ForIR
    {Sig : LogOSSignature lzero}
    {Q : QAdapter lzero}
    (K : GradedKernel Sig Q)
    (toCodeK : UCode → GradedKernel.Code K)
    (fromCodeK : GradedKernel.Code K → UCode)
    (gradeBound : ℕ → QAdapter.Scale Q)
    (Pℕ : PolyPred)
    (brand : UIR.Brand)
    where

    M : UIR.StandardCMᴵᴿ {ℓ = lzero}
    M = UIR.mkIRCM Pℕ brand

    open UIR.StandardCMᴵᴿ M renaming
      ( Input  to Inputᵀ
      ; size   to sizeᵀ
      ; poly   to polyᵀ
      ; wsize  to wsizeᵀ
      )

    module TR = UIR.TR K toCodeK fromCodeK gradeBound M

    WSize : GradedKernel.Code K → ℕ
    WSize w = wsizeᵀ (fromCodeK w)

    module C = ForFromNat
      K Inputᵀ sizeᵀ
      TR.DetRun TR.VerRun TR.VerRunWith
      gradeBound Pℕ

    sizeGrade : ℕ → QAdapter.Scale Q
    sizeGrade = gradeBound

    module WithAccExample {ℓA} (Acc : C.R.Con → Set ℓA) where
      module W = C.WithAcc Acc

      NonDegenerateAt : W.O.LOB → Set _
      NonDegenerateAt lob = W.NonDegenerate lob sizeGrade

    open C public
