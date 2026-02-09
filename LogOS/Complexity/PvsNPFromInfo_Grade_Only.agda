{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.PvsNPFromInfo_Grade_Only where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel.Graded
import LogOS.API.Kernel.Graded.Endo as GEndo
import LogOS.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Complexity.InfoHardnessBridge as IHB
import LogOS.Complexity.PolyGrade as PG
open import LogOS.Complexity.Poly using (PolyPred)
import LogOS.Theorems.Meta.ApplicationKit as AppKit

-- Grade-native convenience constructor: build the TruthRoute P/NP-shaped claim
-- from a total witness interface plus an information bottleneck.

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

  open GradedKernel K

  module R =
    TRG.Uniform
      K Input Size
      (λ x → decode (DetRun x))
      decode
      (GEndo.idEndo K)
      (GEndo.idEndo K)
      (GEndo.idEndo K)
  module G = R.GradeBounded PG

  module WithAcc {ℓA} (Acc : R.Con → Set ℓA) where
    module B = IHB.GenericGradePoly Input Size R.Grade (PG.PolyPredG.isPolyG PG)
               (R.DetWithinAt Acc)
    open B public

    -- Assumption pack for the info-hardness route (grade-native).
    record Assumptions : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
      field
        total-witnessG : G.PolyTotalWitnessedVerificationG Acc
        BtlG        : DetBottleneck
        hardG       : InfoHardness BtlG

    Claim : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA))
    Claim = G.PvsNPClaimG Acc

    derive : Assumptions → Claim
    derive A =
      let
        A' : G.SpectralSeparationAssumptionsG Acc
        A' =
          record
            { total-witnessG   = Assumptions.total-witnessG A
            ; Det-superpolyG = detSuperPolyFromInfo (Assumptions.BtlG A)
                                                  (Assumptions.hardG A)
            }
      in
      G.PvsNPPackG.claim (G.mkPvsNPG A')

    module Q = AppKit.MakeConstPack Assumptions Claim derive
    open Q public using (Pack; assumptionsOf; claimOf; mkPack)

    module WithWitnessSizeG {ℓW}
                             (IsPolyW : (ℕ → ℕ) → Set ℓW)
                             (WSize : GradedKernel.Code K → ℕ)
                             where

      module WG = G.WithWitnessSizeG IsPolyW WSize

      record AssumptionsW : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))) where
        field
          total-witnessWG : WG.PolyTotalWitnessedVerificationWG Acc
          BtlG         : DetBottleneck
          hardG        : InfoHardness BtlG

      ClaimW : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))
      ClaimW = WG.PvsNPClaimWG Acc

      deriveW : AssumptionsW → ClaimW
      deriveW A =
        let
          A' : WG.SpectralSeparationAssumptionsWG Acc
          A' =
            record
              { total-witnessWG   = AssumptionsW.total-witnessWG A
              ; Det-superpolyG = detSuperPolyFromInfo (AssumptionsW.BtlG A)
                                                    (AssumptionsW.hardG A)
              }
        in
        WG.PvsNPPackWG.claim (WG.mkPvsNPWG A')

      module QW = AppKit.MakeConstPack AssumptionsW ClaimW deriveW
      open QW public hiding (mkPack ; assumptionsOf ; claimOf) renaming (Pack to PackW)

      mkPackW : (A : AssumptionsW) → PackW
      mkPackW = QW.mkPack

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
