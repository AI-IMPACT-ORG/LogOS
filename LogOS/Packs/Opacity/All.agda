{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Opacity.All where

-- Opacity pack:
-- - kernel-level opacity infrastructure
-- - conditional application ledger (guarded)

open import LogOS.API.Minimal public

module Opacity where
  open import LogOS.Packs.Opacity.Core public

module GRH where
  open import LogOS.Packs.Opacity.Applications.GRH public
