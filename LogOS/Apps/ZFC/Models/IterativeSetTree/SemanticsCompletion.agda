{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCompletion where

-- Optional same-stage completion witness surfaces.

import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCurrentCompletion
import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsSuccessorCompletion

module CurrentForLevel = LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCurrentCompletion.ForLevel
module SuccessorForLevel = LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsSuccessorCompletion.ForLevel
