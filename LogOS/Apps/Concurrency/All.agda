{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Concurrency.All where

-- Concurrency pack (v1.1).
--
-- Goal: present concurrency as the shared-boundary / many-realisations
-- specialization of the generic locality and transport discipline.
--
-- Entrypoints:
-- - `LogOS/Apps/Concurrency/HappensBefore.agda`
-- - guide: `docs/Patterns/Shared_Distributed_Semantics.lagda.md`
--
-- Implemented now:
-- - the implemented surface is exactly the import below
-- - detailed application narration lives in
--   `docs/Patterns/Shared_Distributed_Semantics.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs

import LogOS.Apps.Concurrency.HappensBefore as HappensBefore
