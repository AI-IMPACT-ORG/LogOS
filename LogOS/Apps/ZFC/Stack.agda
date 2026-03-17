{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack where

-- Curated entrypoint: ZF/ZFC as a stack of logical transformers over one boundary.

import LogOS.Apps.ZFC.Stack.Boundary as Boundary
import LogOS.Apps.ZFC.Stack.ZFCore as ZFCore
import LogOS.Apps.ZFC.Stack.ZFC as ZFC
import LogOS.Apps.ZFC.Stack.MembershipLocality as MembershipLocality
import LogOS.Apps.ZFC.Stack.InfinityUpgrade as InfinityUpgrade
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as ProfileTower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as ProfileTowerFO
import LogOS.Apps.ZFC.Stack.AsymptoticReification as AsymptoticReification
import LogOS.Apps.ZFC.Stack.AsymptoticInfinityUpgrade as AsymptoticInfinityUpgrade
import LogOS.Apps.ZFC.Stack.FoundationUpgradeFO as FoundationUpgradeFO
import LogOS.Apps.ZFC.Stack.WellFounded as WellFounded
import LogOS.Apps.ZFC.Stack.WellFoundedPart as WellFoundedPart
import LogOS.Apps.ZFC.Stack.ReifiedTower as ReifiedTower

module Architecture = ProfileTower
