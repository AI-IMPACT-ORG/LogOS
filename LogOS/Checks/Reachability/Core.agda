{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Reachability.Core where

-- Policy-only reachability root for the default curated API surface and its
-- explicit opt-in companions.

import LogOS.API.LT
import LogOS.API.Guarded
import LogOS.API.Strictification
