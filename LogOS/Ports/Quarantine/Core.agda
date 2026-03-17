{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Quarantine.Core where

-- Quarantine zone for meaning-changing boundary translations.
--
-- Architectural policy:
-- - In the normal codebase, locality-facing semantics are expressed via
--   `LocalBoundary` / `LocalityPort` and their pointwise tooling.
-- - Any construction that *changes the meaning* of a distributed boundary
--   (e.g. coarse-graining, aggregation across indices, non-pointwise reindexing)
--   must live under `LogOS.Ports.Quarantine.*`.
-- - Access to quarantined constructions is only via curated bridge modules
--   under `LogOS.Ports.Bridges.*` (enforced by CI import checks).

open import LogOS.Prelude using (lzero; ⊤; tt)

-- Harmless witness: keeps this module reachable/typechecked without exporting
-- any quarantined API by default.
ok : ⊤ {ℓ = lzero}
ok = tt
