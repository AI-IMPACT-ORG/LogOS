{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis where

-- MetaTheory — A 2-Cell Basis (thinification + shadow factorisation + boundary semantics).
--
-- This entrypoint is intentionally small: it provides a stable navigation
-- module for the mechanised “logic architecture” metatheory.

import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps as TwoCellOps
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat as Strict2Cat
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow as Shadow
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView as ShadowByView
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowInitiality as ShadowInitiality
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext as ObsContext
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.RunningBoundaryGauge as RunningBoundaryGauge
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.UniversalProperties as UniversalProperties
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory as Bicategory
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.PseudoFunctor as PseudoFunctor
