{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ApplicationKit where

-- Small helpers for “application packs” in the LogOS style.
--
-- The core pack skeleton is `QuartetCore` (Assumptions / Claim / Pack / mkPack).
-- This module adds tiny derived wrappers that:
-- - fix a derivation (so `mkPack` is a single-argument constructor), and
-- - optionally expose a `LogicCore` projection for model-theoretic “bundle-first”
--   packaging at the pack surface level.

open import LogOS.Prelude

open import LogOS.API.Assumptions.Core using (LogicCore)
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- Dependent claim: derive `Claim A` from `A`.
module MakeDerived
  {ℓA ℓC : Level}
  (Assumptions : Set ℓA)
  (Claim : Assumptions → Set ℓC)
  (derive : (A : Assumptions) → Claim A)
  where

  module Q = Quartet.Make Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : Assumptions → Pack
  mkPack = Q.mkPack derive

-- Constant claim: `Claim` does not depend on assumptions.
module MakeConstPack
  {ℓA ℓC : Level}
  (Assumptions : Set ℓA)
  (Claim : Set ℓC)
  (derive : (A : Assumptions) → Claim)
  where

  module Base = Quartet.MakeConstPack Assumptions Claim derive
  open Base public using (Pack; assumptionsOf; claimOf; mkPack)

-- Model-theoretic variant: package the `LogicCore` of a pack.
module MakeDerivedWithCore
  {ℓA ℓC ℓCore : Level}
  (Assumptions : Set ℓA)
  (coreOf : Assumptions → LogicCore {ℓCore})
  (Claim : Assumptions → Set ℓC)
  (derive : (A : Assumptions) → Claim A)
  where

  module Q = MakeDerived Assumptions Claim derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

  core : Pack → LogicCore {ℓCore}
  core p = coreOf (assumptionsOf p)
