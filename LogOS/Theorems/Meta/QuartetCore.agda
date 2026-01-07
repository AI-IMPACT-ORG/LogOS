{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.QuartetCore where

-- Reusable core for the “quartet” pack pattern used throughout LogOS:
-- Assumptions / Claim / Pack / mkPack.
--
-- This module is intentionally tiny and structure-free: it only packages
-- existing data into a uniform record shape to reduce boilerplate and avoid
-- drift across application packs.

open import LogOS.Prelude

module Make
  {ℓA ℓC : Level}
  (Assumptions : Set ℓA)
  (Claim : Assumptions → Set ℓC)
  where

  record Pack : Set (ℓA ⊔ ℓC) where
    field
      assumptions : Assumptions
      claim       : Claim assumptions

  mkPack : (derive : (A : Assumptions) → Claim A) → (A : Assumptions) → Pack
  mkPack derive A = record { assumptions = A ; claim = derive A }

  assumptionsOf : Pack → Assumptions
  assumptionsOf = Pack.assumptions

  claimOf : (p : Pack) → Claim (assumptionsOf p)
  claimOf p = Pack.claim p

-- A common special case: the claim does not depend on the assumptions.
-- This avoids repeated `λ _ → Claim` lambdas across packs.

module MakeConst
  {ℓA ℓC : Level}
  (Assumptions : Set ℓA)
  (Claim : Set ℓC)
  where
  open Make Assumptions (λ _ → Claim) public

-- Another common special case: package a fixed derivation into the quartet.
-- This gives the standard `mkPack : Assumptions → Pack` entrypoint.

module MakeConstPack
  {ℓA ℓC : Level}
  (Assumptions : Set ℓA)
  (Claim : Set ℓC)
  (derive : (A : Assumptions) → Claim)
  where

  module Q = MakeConst Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : Assumptions → Pack
  mkPack = Q.mkPack derive
