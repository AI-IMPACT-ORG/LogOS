{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed where

-- Discipline gate: port 2-cats must be displayed + Σ-decorated.
--
-- This targets the `LogOS.Ports/**` 2-category modules.
--
-- This is deliberately a *typecheck gate*: the proofs are `refl`, so the file
-- breaks if a port category stops being definitionally a decoration of a
-- displayed structure (or if an independent stack stops being a displayed
-- product with canonical projections).

open import LogOS.Prelude using (lzero; ⊤; tt)

import LogOS.Ports.Discipline.PortsAsDisplayed.Core
import LogOS.Ports.Discipline.PortsAsDisplayed.Local
import LogOS.Ports.Discipline.PortsAsDisplayed.Budget
import LogOS.Ports.Discipline.PortsAsDisplayed.Deutsch
import LogOS.Ports.Discipline.PortsAsDisplayed.PreQuantum
import LogOS.Ports.Discipline.PortsAsDisplayed.Coverage

-- The theorem graph for this discipline lives in the imported submodules.
-- Policy-only wrapper reachability is handled separately in
-- `LogOS.Checks.Reachability.Ports`, so this entrypoint stays aligned with the
-- actual displayed/decoration proof sites.

-- Export one harmless witness so this module can be imported via the API
-- without re-exporting all internal discipline lemmas.
ok : ⊤ {ℓ = lzero}
ok = tt
