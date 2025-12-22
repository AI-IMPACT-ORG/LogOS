{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
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

    record Pack (A : Assumptions) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
      field
        assumptions : Assumptions
        claim       : Claim

    mkPack : (A : Assumptions) → Pack A
    mkPack A =
      let
        A' : G.SpectralSeparationAssumptionsG Acc
        A' =
          record
            { NP-witnessG   = Assumptions.NP-witnessG A
            ; Det-superpolyG = detSuperPolyFromInfo (Assumptions.BtlG A)
                                                  (Assumptions.hardG A)
            }
      in
      record
        { assumptions = A
        ; claim       = G.PvsNPPackG.claim (G.mkPvsNPG A')
        }

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

      record PackW (A : AssumptionsW) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))) where
        field
          assumptions : AssumptionsW
          claim       : ClaimW

      mkPackW : (A : AssumptionsW) → PackW A
      mkPackW A =
        let
          A' : WG.SpectralSeparationAssumptionsWG Acc
          A' =
            record
              { NP-witnessWG   = AssumptionsW.NP-witnessWG A
              ; Det-superpolyG = detSuperPolyFromInfo (AssumptionsW.BtlG A)
                                                    (AssumptionsW.hardG A)
              }
        in
        record
          { assumptions = A
          ; claim       = WG.PvsNPPackWG.claim (WG.mkPvsNPWG A')
          }

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
