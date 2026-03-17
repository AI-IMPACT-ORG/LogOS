{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureEncode2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Encode port over the architecture-first implementation basis `LOGᴳʳ`.
--
-- Reading:
-- - architecture: `LOGᴳ`
-- - implementation: `LOGᴳʳ`
-- - law: encode coherence reindexed from the façade-level encode port

open import LogOS.Prelude
open import LogOS.LT.LOG.Implementation2Cat.Core using (LOGᴳʳ)

import LogOS.LT.LOG.EncodePort2Cat as Encode
import LogOS.LT.LOG.PortReindexing.Strictification as PortReindexing

open Encode public using (EncodeTag; encodeTag)

module Port {ℓ ℓRel ℓCode : Level} =
  PortReindexing.PullbackSingletonExportsAlongToLOG
    (Encode.encodeSig {ℓ} {ℓRel} {ℓCode})

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)
