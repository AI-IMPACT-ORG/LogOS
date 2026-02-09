{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.GRHLedger where

-- GRH/RH in LogOS is an *axiom ledger* / *reverse-mathematics template*:
-- we isolate the exact interfaces and guards under which a GRH-shaped statement
-- follows, without claiming a classical analytic proof of GRH/RH.
--
-- Canonical guarded surface (packaged GRH/RH claim with explicit vacuity guards).
open import LogOS.Domain.Opacity.GRH_Vacuity_Guards public

