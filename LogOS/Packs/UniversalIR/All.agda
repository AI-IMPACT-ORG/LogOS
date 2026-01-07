{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.All where

-- UniversalIR pack:
-- - curated computational universality surface (“machines as schemes”)
-- - multi-paradigm agreement theorem
-- - kernel instance + boundary I/O views

open import LogOS.API.Minimal public

module Core where
  open import LogOS.Packs.UniversalIR.Core public

module Agreement where
  open import LogOS.Packs.UniversalIR.Agreement public

module Algorithms where
  open import LogOS.Packs.UniversalIR.Pack public

module Examples where
  open import LogOS.Packs.UniversalIR.Examples public

module KernelInstance where
  open import LogOS.Packs.UniversalIR.Kernel public
