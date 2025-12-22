{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.All where

-- Lean re-exports of port-level theorems (view adapters and decode-level
-- facts within a kernel).

open import LogOS.Theorems.Laws.FiniteKernel.S public  -- S ↔ H coherence ports
open import LogOS.Theorems.Code.Core  public  -- Guarded decode-level ports (reify/body/naturality)
