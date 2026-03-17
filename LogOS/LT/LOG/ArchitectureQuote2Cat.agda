{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureQuote2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Quote port over the architecture-first implementation basis `LOGᴳʳ`.

import LogOS.LT.LOG.QuotePort2Cat.Port as Port
import LogOS.LT.LOG.ArchitectureQuote2Cat.Displayed as Displayed

open Port public
open Displayed public
