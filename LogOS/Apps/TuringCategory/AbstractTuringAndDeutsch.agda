{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.AbstractTuringAndDeutsch where

-- Side-by-side navigation of two category-theoretic “universality” stories that
-- are intentionally kept separate in v1.1:
--
-- (1) Turing categories (CH2008): internal universality for *partial maps*
--     inside a restriction category (indexing into a fixed object `U`).
--
-- (2) The Deutsch-style category: a port stack over dependent physical semantics
--     (locality + causality + local reversibility), presented as a thin 2-category.
--
-- There is no theorem in-tree that identifies these. Any bridge would have to
-- be explicit about:
-- - the chosen observation boundary (`View`) and any “classicalisation” step,
-- - which fragment of physical morphisms is being compared to partial maps, and
-- - what is claimed up to refinement vs strict equality.
--
-- Structural comparison aid (implemented):
-- `LogOS.Apps.TuringCategory.Bridge` provides functors `LOG → Par` and
-- `LOGᴰ PS → Par` (and optional lifts into `ParTracked U TU`), for comparing
-- shapes without asserting a universality theorem.

import LogOS.Apps.TuringCategory.CH2008 as CH
import LogOS.Apps.TuringCategory.ParCH2008 as ParCH
import LogOS.Apps.TuringCategory.ParTuring as CT
import LogOS.Apps.TuringCategory.ParTracked as CTTracked
import LogOS.Apps.TuringCategory.Bridge as Bridge

import LogOS.Ports.AbstractDeutsch2Cat as Deutsch
import LogOS.Ports.AbstractDeutschNoCloning as NoCloning
