{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Reachability.Ports where

-- Policy-only reachability root for optional port surfaces that remain
-- intentionally off the default curated API surface.

import LogOS.Ports.Globalise
import LogOS.API.Ports.PhysicalOptional
import LogOS.API.Ports.PhysicalOptional.Causal
import LogOS.API.Ports.PhysicalOptional.Landauer
import LogOS.API.Ports.PhysicalOptional.Deutsch
import LogOS.API.Ports.PhysicalOptional.PreQuantum
import LogOS.API.Ports.UniversalityLOG
import LogOS.API.Ports.LTDecorationsLOG
import LogOS.Ports.All
import LogOS.Ports.IO.Definitional
import LogOS.Ports.BoundaryAsCode.Definitional
import LogOS.Ports.BoundaryTransparency.Definitional
import LogOS.Ports.Locality.Definitional
import LogOS.Ports.Opacity.Port.Definitional
import LogOS.Ports.AbstractDeutsch2Cat
import LogOS.Ports.AbstractDeutsch2Cat.Definitional
import LogOS.Ports.AbstractDeutsch2Cat.DeutschProduct
import LogOS.Ports.AbstractCausal2Cat
import LogOS.Ports.AbstractCausalLandauer2Cat
import LogOS.Ports.AbstractLandauerStack2Cat
import LogOS.Ports.AbstractDeutschNoCloning
import LogOS.Ports.AbstractLandauer2Cat
import LogOS.Ports.AbstractLandauerObservational
import LogOS.Ports.Discipline.PortsAsDisplayed
import LogOS.Ports.Discipline.PortsAsDisplayed.ArchitectureLaws
import LogOS.Ports.AbstractLandauer.Ledger
import LogOS.Ports.CriticalParameter
import LogOS.Ports.Dynamics.Action
import LogOS.Ports.PreQuantum.AbstractCausalPreQuantum2Cat
import LogOS.Ports.PreQuantum.Monoidal
import LogOS.Ports.PreQuantum.Discard
import LogOS.Ports.PreQuantum.Discard2Cat
import LogOS.Ports.PreQuantum.Purification
import LogOS.Ports.PreQuantum.Purification2Cat
import LogOS.Ports.Realisations.DependentStack
import LogOS.Ports.Realisations.Architecture
import LogOS.Ports.PhysicalSemantics.Ledger
import LogOS.Ports.Universality.ArchitectureBudgetBus2Cat
import LogOS.Ports.Universality.Agreement.Definitional
import LogOS.Ports.Universality.ArchitectureFlowBudget2Cat
import LogOS.Ports.Universality.BudgetBus2Cat
import LogOS.Ports.Universality.Definitional
import LogOS.Ports.Universality.FlowBudget2Cat
import LogOS.Ports.Valuation.QAdapter.Definitional
import LogOS.Ports.Valuation.QAdapterBudgetTransport2Cat
