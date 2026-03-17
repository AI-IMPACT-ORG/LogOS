{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.All where

-- Adapters (implementations of ports).
--
-- Concrete instances that implement port interfaces from `LogOS/Ports/**`.
-- For kernel-level ports that are displayed layers over `LOG`, the “adapter
-- obligations” live as the displayed morphism data (see
-- `LogOS/LT/DisplayedThin2Cat.agda`).
--
-- Directionality (hexagonal discipline): adapters may import ports; ports must
-- not import adapters.
--
-- Adapters should be thin, explicit, and compositional:
-- - prefer composing smaller adapters over building monoliths
-- - keep assumptions explicit (as records/parameters), not implicit meta-claims

import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Adapters.Universality.Lambda as Lambda
import LogOS.Adapters.Universality.EVM as EVM
import LogOS.Adapters.Universality.PreQuantum as PreQuantum
import LogOS.Adapters.Universality.PreQuantumCircuit as PreQuantumCircuit
