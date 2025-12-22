{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PvsNP where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded
import LogOS.Domain.Complexity.PolyGrade as PG
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG

-- P vs NP surface (language-relative + correctness) over a graded kernel.

module For
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (PGG : PG.PolyPredG (QAdapter.Scale Q))
  (IsPolyW : (ℕ → ℕ) → Set ℓP)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module R = TRG.For K Input Size DetRun VerRun VerRunWith
  module G = R.GradeBounded PGG
  module W = G.WithWitnessSizeG IsPolyW WSize

  record Assumptions (ℓL : Level) (Lang : R.Language ℓL)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
    field
      NP-holds : W.InNPG {ℓL = ℓL} Lang
      notP     : ¬ G.InPG {ℓL = ℓL} Lang

  record Claim (ℓL : Level) (Lang : R.Language ℓL)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
    field
      NP-holds : W.InNPG {ℓL = ℓL} Lang
      notP     : ¬ G.InPG {ℓL = ℓL} Lang

  -- This layer is packaging only: assumptions are rewrapped as the claim.
  assumptions→claim : ∀ {ℓL} {Lang : R.Language ℓL} → Assumptions ℓL Lang → Claim ℓL Lang
  assumptions→claim A =
    record
      { NP-holds = Assumptions.NP-holds A
      ; notP     = Assumptions.notP A
      }

  record Pack {ℓL} (Lang : R.Language ℓL)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
    field
      assumptions : Assumptions ℓL Lang
      claim       : Claim ℓL Lang

  mkPack
    : ∀ {ℓL} {Lang : R.Language ℓL}
      → Assumptions ℓL Lang → Pack Lang
  mkPack A = record { assumptions = A ; claim = assumptions→claim A }
