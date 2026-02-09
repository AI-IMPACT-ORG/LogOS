{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.All where

-- Index module for the ObjectLogic topic library (discoverability only).

import LogOS.ObjectLogic.FOL.All as FOLₜ
import LogOS.ObjectLogic.ZFC.All as ZFCₜ

module FOL = FOLₜ
module ZFC = ZFCₜ

