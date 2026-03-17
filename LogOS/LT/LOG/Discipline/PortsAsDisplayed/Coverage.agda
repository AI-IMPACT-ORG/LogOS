{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Discipline.PortsAsDisplayed.Coverage where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Policy-only coverage module:
-- keep canonical LOG `*2Cat` wrappers in the discipline closure without
-- forcing the lightweight API witness module to import them directly.

import LogOS.LT.LOG.ArchitectureFlowContract2Cat
import LogOS.LT.LOG.ArchitectureBulkBoundaryContract2Cat
