{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Assumptions.All where

-- Convenience umbrella: import the shared logic core + the three orthogonal
-- domain bundles, plus a single `AssumeAll` record if you want “assume all”.

open import LogOS.Prelude

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

open import LogOS.API.Assumptions.Core public
open import LogOS.Packs.Assumptions.ZFC public
open import LogOS.Packs.Assumptions.Universality public
open import LogOS.Packs.Assumptions.Physics public

module Separation where
  open import LogOS.Packs.Assumptions.Separation public

record AssumeAll {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    core : LogicCore {ℓ}
    zfc  : ZFCBundle core
    uni  : UniversalityBundle core
    phys : PhysicsOfInformationBundle core

open AssumeAll public
