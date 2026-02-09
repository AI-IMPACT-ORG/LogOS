{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Safety.NoTotalAuditor where

-- Optional, experimental instantiation via the complexity/opacity spine.

open import LogOS.Packs.Agents.Safety.NoTotalAuditor public

import LogOS.Packs.Complexity.Experimental.ProofSearchOpacitySpine as ProofSearchOpacitySpineₜ
module ProofSearchOpacity = ProofSearchOpacitySpineₜ
