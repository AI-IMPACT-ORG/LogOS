{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.CTD.Ledger where

-- Universality ledger in a CTD-style reading.
--
-- This module is intentionally minimal and assumption-scoped:
--
-- - pick a “universal” kernel `U` (the simulator) with a closure `GCᵁ` (effective law),
-- - model each physical system as a kernel `K s` with its own closure `GC s`,
-- - require a *flow-preserving* adapter into `U`.
--
-- The main derived corollary is the tooling loop:
-- flow-preserving simulation commutes with effectivisation/normalisation
-- (up to refinement) via `LogOS.LT.Theorems.Effectivisation`.

open import LogOS.Prelude
open import LogOS.Ports.Universality.CTD.Core using (FlowSimulationFamily)

record CTDLedger {ℓ ℓRel ℓCode ℓSys : Level}
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓSys)) where
  field
    simulations : FlowSimulationFamily {ℓ} {ℓRel} {ℓCode} {ℓSys}

  open FlowSimulationFamily simulations public

open CTDLedger public
-- The code does not prove the full Church-Turing-Deutsch principle. It
-- packages one assumption-scoped universality shape: a chosen universal kernel
-- plus flow-preserving simulations into it.
