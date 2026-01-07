{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.All where

-- Computational universality pack (UniversalIR-first):
-- - UniversalIR core + multi-paradigm agreement
-- - a meta-language refinement (schemes/processes + functorial contracts)

open import LogOS.API.Minimal public

module UniversalIR where
  open import LogOS.Packs.UniversalIR.Core public

module Agreement where
  open import LogOS.Packs.UniversalIR.Agreement public

module Algorithms where
  open import LogOS.Packs.UniversalIR.Pack public

module MetaLanguage where
  open import LogOS.MetaLanguage.All public

module Toy where
  open import LogOS.Packs.Universality.Core public
