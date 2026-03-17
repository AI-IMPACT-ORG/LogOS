{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.QuotePort2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Guarded self-reference as a port (encode + flow + a linking law).
--
-- This is the code-level counterpart of partial reflection:
-- encoding a boundary constraint as code, then decoding it back, yields the
-- *normalised* boundary constraint (not raw identity).
--
-- The safety valve is `Flow`: self-reference is only available up to a guarded
-- closure (KZ-style modality), not as an unrestricted fixed-point principle.

-- Large LT module split into:
-- - `QuotePort2Cat.FlowEncodeLayer` : the independent flow/encode envelope layer
-- - `QuotePort2Cat.Port`           : quote port data + canonical construction
-- - `QuotePort2Cat.Displayed`      : displayed structure + totalised 2-category

import LogOS.LT.LOG.QuotePort2Cat.FlowEncodeLayer as FlowEncodeLayer
import LogOS.LT.LOG.QuotePort2Cat.Port as Port
import LogOS.LT.LOG.QuotePort2Cat.Displayed as Displayed

open FlowEncodeLayer public
open Port public
open Displayed public
