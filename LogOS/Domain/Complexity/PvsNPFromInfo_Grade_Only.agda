{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Domain.Complexity.InfoHardnessBridge as IHB
import LogOS.Domain.Complexity.PolyGrade as PG
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- Grade-native convenience constructor: build the TruthRoute PvsNP claim from
-- an NP witness plus an information bottleneck interface.

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
  (PG : PG.PolyPredG (QAdapter.Scale Q))
  where

  module R = TRG.For K Input Size DetRun VerRun VerRunWith
  module G = R.GradeBounded PG

  module WithAcc {ℓA} (Acc : R.Con → Set ℓA) where
    module B = IHB.GenericGradePoly Input Size R.Grade (PG.PolyPredG.isPolyG PG)
               (R.DetWithinAt Acc)
    open B public

    -- Assumption pack for the info-hardness route (grade-native).
    record Assumptions : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
      field
        NP-witnessG : G.PolyWitnessedTotalVerificationG Acc
        BtlG        : DetBottleneck
        hardG       : InfoHardness BtlG

    Claim : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA))
    Claim = G.PvsNPClaimG Acc

    module Q = Quartet.Make Assumptions (λ _ → Claim)
    open Q public using (Pack; assumptionsOf; claimOf)

    mkPack : (A : Assumptions) → Pack
    mkPack A =
      Q.mkPack
        (λ A →
          let
            A' : G.SpectralSeparationAssumptionsG Acc
            A' =
              record
                { NP-witnessG   = Assumptions.NP-witnessG A
                ; Det-superpolyG = detSuperPolyFromInfo (Assumptions.BtlG A)
                                                      (Assumptions.hardG A)
                }
          in
          G.PvsNPPackG.claim (G.mkPvsNPG A'))
        A

    module WithWitnessSizeG {ℓW}
                             (IsPolyW : (ℕ → ℕ) → Set ℓW)
                             (WSize : GradedKernel.Code K → ℕ)
                             where

      module WG = G.WithWitnessSizeG IsPolyW WSize

      record AssumptionsW : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))) where
        field
          NP-witnessWG : WG.PolyWitnessedTotalVerificationWG Acc
          BtlG         : DetBottleneck
          hardG        : InfoHardness BtlG

      ClaimW : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))
      ClaimW = WG.PvsNPClaimWG Acc

      module QW = Quartet.Make AssumptionsW (λ _ → ClaimW)
      open QW public hiding (mkPack ; assumptionsOf ; claimOf) renaming (Pack to PackW)

      mkPackW : (A : AssumptionsW) → PackW
      mkPackW A =
        QW.mkPack
          (λ A →
            let
              A' : WG.SpectralSeparationAssumptionsWG Acc
              A' =
                record
                  { NP-witnessWG   = AssumptionsW.NP-witnessWG A
                  ; Det-superpolyG = detSuperPolyFromInfo (AssumptionsW.BtlG A)
                                                        (AssumptionsW.hardG A)
                  }
            in
            WG.PvsNPPackWG.claim (WG.mkPvsNPWG A'))
          A

-- Convenience adapter: lift PolyPred via a gradeBound into the grade-native route.
module FromNat
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (Pℕ : PolyPred)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  module PGN = PG.FromNat Q Pℕ gradeBound
  module Core = For K Input Size DetRun VerRun VerRunWith PGN.polyPredG
  open Core public
