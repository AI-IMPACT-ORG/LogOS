{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.CTandCTD where

-- Side-by-side navigation of two “universality” shapes that both feature a
-- distinguished object `U`, but live in different ambient categories.
--
-- (1) CH(2008) Turing-category shape (CT-like):
--     internal “universal evaluation” + indexing of *morphisms* into a fixed `U`.
--     In this pack: `LogOS.Apps.TuringCategory.CH2008` and `ParTuring`.
--
-- (2) CTD shape (Deutsch object / weak terminality in `LOGᶠ`):
--     flow-preserving simulations of *systems* into a universal kernel `U`.
--     In the wider repo: `LogOS.Ports.Universality.CTD.Ledger` and the concrete instance
--     `LogOS.Apps.Universality.CTD`.
--
-- This module is navigation-only: it asserts no theorem connecting (1) and (2).

import LogOS.Apps.TuringCategory.CH2008 as CH
import LogOS.Apps.TuringCategory.ParTuring as CT

import LogOS.Ports.Universality.CTD.Ledger as CTD
import LogOS.Apps.Universality.CTD as CTDApp

