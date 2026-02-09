{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Trust where

-- Minimal trust taxonomy for pack surfaces and documentation cross-references.

data TrustLevel : Set where
  -- `stable`: intended user-facing surface; relatively stable APIs and semantics.
  --
  -- `experimental`: under active development; APIs/claims may change materially.
  --
  -- `scaffold`: structural wiring / demo-grade infrastructure. These modules can
  -- be perfectly well typechecked, but are often intentionally vacuous (e.g.
  -- top orders, trivial truth) and should not be read as substantive semantic
  -- claims without additional non-vacuity assumptions.
  --
  -- `deprecated`: migration marker; use the recommended replacement surfaces.
  stable experimental scaffold deprecated : TrustLevel

record PackTrust : Set where
  field
    level : TrustLevel
