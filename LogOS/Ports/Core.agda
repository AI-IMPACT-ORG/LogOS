{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Core where

-- Core port interfaces (no tooling or “full umbrella” re-exports).

open import LogOS.Ports.Semantic.Core public
open import LogOS.Ports.Telemetry.Core public
open import LogOS.Ports.SpectralPack public

