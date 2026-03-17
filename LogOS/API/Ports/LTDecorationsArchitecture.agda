{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.LTDecorationsArchitecture where

-- Curated re-exports for architecture-first LT decorations.
--
-- Reading:
-- - architecture: `LOGᴳ` and the boundary-only stacks that live on it directly
-- - implementation: `LOGᴳʳ`
-- - law: displayed ports and port stacks layered on top
--
-- Optional physical doctrine witnesses stay out of this curated shell.
-- Import `LogOS.Ports.Discipline.PortsAsDisplayed.ArchitectureLaws`
-- explicitly if a development wants that policy-only witness.

open import LogOS.LT.DisplayedThin2Cat public
open import LogOS.LT.HomFlow public

import LogOS.LT.LOG.ImplementationFlow2Cat.Core as ImplementationFlow
import LogOS.LT.LOG.ImplementationContract2Cat.Core as ImplementationContract
import LogOS.LT.LOG.ArchitectureEncode2Cat as ArchitectureEncode
import LogOS.LT.LOG.ArchitectureFlowContract2Cat as ArchitectureFlowContract
import LogOS.LT.LOG.ArchitectureBulkBoundary2Cat as ArchitectureBulkBoundary
import LogOS.LT.LOG.ArchitectureBulkBoundaryContract2Cat as ArchitectureBulkBoundaryContract
import LogOS.LT.LOG.ArchitectureQuote2Cat as ArchitectureQuote

open import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Laws public renaming (ok to ltPortsAsDisplayed-ok)
