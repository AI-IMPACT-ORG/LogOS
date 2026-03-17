{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.QuotePort2Cat.FlowEncodeLayer where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
import LogOS.LT.LOG.Flow2Cat as Flow2Cat
import LogOS.LT.LOG.EncodePort2Cat as Encode2Cat

import LogOS.LT.Ports.PortStack.Raw as PortStack

FlowEncodeStack
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})
FlowEncodeStack {ℓ} {ℓRel} {ℓCode} =
  PortStack.SingletonPort.entry (Flow2Cat.singleton {ℓ} {ℓRel} {ℓCode})
    PortStack.∷⁺
    PortStack.SingletonPort.stack (Encode2Cat.singleton {ℓ} {ℓRel} {ℓCode})
