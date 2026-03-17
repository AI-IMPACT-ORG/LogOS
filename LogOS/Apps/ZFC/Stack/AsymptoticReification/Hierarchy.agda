{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.Hierarchy where

-- Canonical stage-by-stage hierarchy packaging for ZFC-style late collapse.
--
-- Compatibility facade over the split canonical-rung / successor-hierarchy
-- packaging.

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as Canonical
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorHierarchy as Successor

open Canonical public using (CanonicalRung)
open Successor public using (SuccessorHierarchy)
