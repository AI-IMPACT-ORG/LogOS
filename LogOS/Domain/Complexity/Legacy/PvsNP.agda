{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Legacy.PvsNP where

-- Legacy: packaging-only PvsNP wrapper; prefer grade-only or info routes.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded
import LogOS.Domain.Complexity.PolyGrade as PG
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Theorems.Meta.QuartetCore as Quartet

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

  -- Packaging-only: the claim is definitionally the assumptions.
  Claim : (ℓL : Level) → R.Language ℓL → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP)))
  Claim = Assumptions

  -- This layer is packaging only: assumptions are rewrapped as the claim.
  assumptions→claim : ∀ {ℓL} {Lang : R.Language ℓL} → Assumptions ℓL Lang → Claim ℓL Lang
  assumptions→claim A = A

  module Q {ℓL} {Lang : R.Language ℓL} =
    Quartet.Make (Assumptions ℓL Lang) (λ _ → Claim ℓL Lang)
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack
    : ∀ {ℓL} {Lang : R.Language ℓL}
      → Assumptions ℓL Lang → Pack {ℓL} {Lang}
  mkPack A =
    Q.mkPack (λ A → assumptions→claim A) A
