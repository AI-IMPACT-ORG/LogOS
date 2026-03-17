{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.LTDecorations where

-- Curated re-exports for displayed/Σ-totalised LT port categories.
-- Default is the architecture-first basis; LOG-basis is available explicitly under `LTDecorations.LOG`.

open import LogOS.API.Ports.LTDecorationsArchitecture public
import LogOS.API.Ports.LTDecorationsLOG

module LOG = LogOS.API.Ports.LTDecorationsLOG
