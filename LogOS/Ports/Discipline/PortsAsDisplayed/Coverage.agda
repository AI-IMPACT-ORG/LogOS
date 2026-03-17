{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.Coverage where

-- Policy-only coverage module:
-- keep canonical physical `*2Cat` wrappers in the discipline closure without
-- forcing the lightweight API witness module to import them directly.

import LogOS.Ports.Universality.ArchitectureBudgetBus2Cat
import LogOS.Ports.Universality.ArchitectureFlowBudget2Cat
