{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Surface where

-- Navigation surface for domain developments (NOT a publication-facing API).
--
-- Pack users should import `LogOS.Packs.*.Surface` instead.

import LogOS.ZFC.Surface as ZFCₛ
import LogOS.InfoTheory.Surface as InfoTheoryₛ
import LogOS.Domain.All as Domainₐ
import LogOS.Complexity.Surface as Complexityₛ
import LogOS.Universality.All as Universalityₐ
import LogOS.Universality.Surface as Universalityₛ
import LogOS.UniversalIR.Surface as UniversalIRₛ
import LogOS.ObjectLogic.Surface as ObjectLogicₛ

module ZFC = ZFCₛ
module InfoTheory = InfoTheoryₛ
module Opacity = Domainₐ.Opacity
module Complexity = Complexityₛ
module Universality = Universalityₛ
module UniversalIR = UniversalIRₛ
module ObjectLogic = ObjectLogicₛ
