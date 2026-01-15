{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Trust where

-- Minimal trust taxonomy for pack surfaces and documentation cross-references.

data TrustLevel : Set where
  stable experimental : TrustLevel

record PackTrust : Set where
  field
    level : TrustLevel
