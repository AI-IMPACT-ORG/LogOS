{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Reification where

-- Explicit optional surface for reification and quoted self-reference layers.
--
-- This is intentionally not re-exported by `LogOS.API.LT`.

open import LogOS.Ports.Reification public
open import LogOS.Ports.Reification.Admissible public
open import LogOS.Ports.Reification.Staged public
open import LogOS.Ports.Reification.CrossStage public
open import LogOS.Ports.Reification.GuardedLawvere public
