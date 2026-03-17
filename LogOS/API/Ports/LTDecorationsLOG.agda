{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.LTDecorationsLOG where

-- Curated re-exports for LOG-basis displayed/Σ-totalised LT port categories.
--
-- Policy:
-- this module does not flatten port namespaces or provide bespoke alias names.
-- Consumers should access port data via the imported module namespaces
-- (e.g. `Flow.WithPort`, `Flow.port`, `Flow.forget`).
--
-- Strictification stays explicit under `LogOS.API.Ports.LTStrictificationLOG`.
-- Optional physical doctrine witnesses stay explicit and are not re-exported
-- from this LOG-basis shell.

open import LogOS.LT.DisplayedThin2Cat public

open import LogOS.LT.HomFlow public

-- LOG-basis ports (singleton layers).
import LogOS.LT.LOG.Flow2Cat as Flow
import LogOS.LT.LOG.Contract2Cat as Contract
import LogOS.LT.LOG.EncodePort2Cat as Encode
import LogOS.LT.LOG.QuotePort2Cat as Quote

-- Discipline gates (typecheck-only): ports must be displayed + decorated.
-- These intentionally export only a single harmless witness each.
open import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Laws public renaming (ok to ltPortsAsDisplayed-ok)
