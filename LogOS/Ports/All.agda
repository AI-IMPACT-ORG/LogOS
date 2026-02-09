{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.All where

-- Power-user port umbrella: semantic ports + telemetry + auxiliary port interfaces.
--
-- Prefer `LogOS.Ports.Surface` unless you explicitly want the larger namespace.

open import LogOS.Ports.Semantic.All public
open import LogOS.Ports.Telemetry.All public
open import LogOS.Ports.SpectralPack public
