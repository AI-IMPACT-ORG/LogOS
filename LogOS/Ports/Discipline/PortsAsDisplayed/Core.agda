{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.Core where

-- Discipline gate: port 2-cats must be displayed + Σ-decorated.
--
-- This targets the `LogOS.Ports/**` 2-category modules.
--
-- This is deliberately a *typecheck gate*: the proofs are `refl`, so the file
-- breaks if a port category stops being definitionally a decoration of a
-- displayed structure (or if an independent stack stops being a displayed
-- product with canonical projections).

import LogOS.Ports.Discipline.PortsAsDisplayed.BudgetDefinitional
import LogOS.Ports.Discipline.PortsAsDisplayed.DeutschDefinitional
import LogOS.Ports.Discipline.PortsAsDisplayed.PreQuantumDefinitional
