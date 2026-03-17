{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.All where

-- Logic architecture pack (metatheory basis).
--
-- Goal: host “meta-theory explanations” as mechanised *application modules*:
-- why the LT stack is built around thin 2-categories, how richer categorical
-- presentations factor through a thin shadow, and how explicit boundary
-- semantics induce canonical approximations.
--
-- Entrypoints:
-- - `LogOS/Apps/LogicArchitecture/MetaTheory/Basis.agda` (navigation module)
-- - guide: `docs/Core/MetaTheory/Basis.lagda.md`
--
-- Implemented now:
-- - the implemented surface is exactly the import below
-- - detailed metatheory narration lives in
--   `docs/Core/MetaTheory/Basis.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs

import LogOS.Apps.LogicArchitecture.MetaTheory.Basis as Basis
