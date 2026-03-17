{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.UniversalityLOG where

-- Curated port surfaces for the universality stack showcase (LOG basis).

open import LogOS.API.Ports.UniversalityCommon public

import LogOS.Ports.Universality.BudgetBus2Cat as BudgetBus
import LogOS.Ports.Universality.FlowBudget2Cat as FlowBudget
