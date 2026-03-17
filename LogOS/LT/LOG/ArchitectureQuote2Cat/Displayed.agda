{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureQuote2Cat.Displayed where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Quote port over the architecture-first implementation basis `LOGᴳʳ`.

open import LogOS.Prelude
open import LogOS.LT.LOG.Implementation2Cat.Core using (LOGᴳʳ)

import LogOS.LT.LOG.QuotePort2Cat.Displayed as QuoteLOG
import LogOS.LT.LOG.PortReindexing.Strictification as PortReindexing

module Port {ℓ ℓRel ℓCode : Level} =
  PortReindexing.PullbackSingletonExportsAlongToLOG
    (QuoteLOG.QuoteLayer {ℓ} {ℓRel} {ℓCode})

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)
