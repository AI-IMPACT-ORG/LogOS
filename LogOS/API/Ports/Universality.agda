{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.Universality where

-- Curated port surfaces for the universality stack showcase.
-- Default is the architecture-first basis; LOG-basis is available explicitly under `Universality.LOG`.
-- The flagship app-side façade lives in
-- `LogOS/Apps/Universality/Architecture.agda`.

open import LogOS.API.Ports.UniversalityArchitecture public
import LogOS.API.Ports.UniversalityLOG

module LOG = LogOS.API.Ports.UniversalityLOG

import LogOS.Ports.CriticalParameter as Critical
