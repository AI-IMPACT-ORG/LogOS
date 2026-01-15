{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Experimental.All where

-- Physics-of-information / complexity pack (experimental):
-- - verification vs search centerpiece
-- - physics-of-information axiom/theorem surfaces
-- - conditional separation surfaces (model-driven)
-- - UniversalIR instantiation shell (optional)

open import LogOS.Packs.Trust using (PackTrust; experimental)

packTrust : PackTrust
packTrust = record { level = experimental }

open import LogOS.API.Minimal public

module Core where
  open import LogOS.Packs.Complexity.Experimental.Core public

module PhysicsOfInformation where
  open import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation public

module PvsNP where
  open import LogOS.Packs.Complexity.Experimental.PvsNP.Public public

module UniversalIRCM where
  open import LogOS.Domain.Complexity.UniversalIRCM public
