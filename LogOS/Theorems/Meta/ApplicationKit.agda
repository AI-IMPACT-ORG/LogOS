{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem)

-- ---------------------------------------------------------------------------
-- SatSystem view (bridge): “packs as systems of assumption-indexed claims”
--
-- Note: this file uses `SatSystem` (Ctx/Con/Sat), not an open `LogOS.System.System`.
-- ---------------------------------------------------------------------------

-- Every `Assumptions` type induces a canonical `System` whose constraints are
-- predicates/claims over assumptions, and whose satisfaction is evaluation.
--
-- This makes the quartet shape (Assumptions / Claim / derive) fit the same
-- semantic spine as boundary systems/ports: assumptions are contexts, and
-- claims are constraints whose meaning is “holds under these assumptions”.

claimsSystem
  : ∀ {ℓA ℓC : Level}
    (Assumptions : Set ℓA)
  → SatSystem {ℓCtx = ℓA} {ℓCon = ℓA ⊔ lsuc ℓC} {ℓSat = ℓC}
claimsSystem {ℓC = ℓC} Assumptions =
  satSystem
    Assumptions
    (Assumptions → Set ℓC)
    (λ A φ → φ A)

-- Dependent claim: derive `Claim A` from `A`.
module MakeDerived
  {ℓA ℓC : Level}
  (Assumptions : Set ℓA)
  (Claim : Assumptions → Set ℓC)
  (derive : (A : Assumptions) → Claim A)
  where

  module Q = Quartet.Make Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  systemOfClaims : SatSystem {ℓCtx = ℓA} {ℓCon = ℓA ⊔ lsuc ℓC} {ℓSat = ℓC}
  systemOfClaims = claimsSystem Assumptions

  claimSatisfied : ∀ A → SatSystem.Sat systemOfClaims A Claim
  claimSatisfied = derive

  packSatisfiesClaim : (p : Pack) → SatSystem.Sat systemOfClaims (assumptionsOf p) Claim
  packSatisfiesClaim p = claimOf p

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

  systemOfClaims : SatSystem {ℓCtx = ℓA} {ℓCon = ℓA ⊔ lsuc ℓC} {ℓSat = ℓC}
  systemOfClaims = claimsSystem Assumptions

  claimSatisfied : ∀ A → SatSystem.Sat systemOfClaims A (λ _ → Claim)
  claimSatisfied = derive

  packSatisfiesClaim : (p : Pack) → SatSystem.Sat systemOfClaims (assumptionsOf p) (λ _ → Claim)
  packSatisfiesClaim p = claimOf p

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
