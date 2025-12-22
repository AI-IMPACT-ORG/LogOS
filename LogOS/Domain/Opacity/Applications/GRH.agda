{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH where

-- GRH as an application of the Opacity strand.
--
-- This namespace is intentionally application-facing: it provides conditional
-- theorems that close the GRH/RH claim once you supply:
-- - an analytic criterion (e.g. Weil’s criterion, packaged as a probe lemma),
-- - and an explicit observability/positivity interface.
--
-- The Opacity strand itself (ledgers, observability, opacity/barrier theorems)
-- lives under `LogOS.Domain.Opacity.*`.

open import LogOS.Domain.Opacity.Applications.GRH.HPGRHPack public
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit public
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimitOmegaSup public

open import LogOS.Domain.Opacity.Applications.GRH.ZetaBridge public
open import LogOS.Domain.Opacity.Applications.GRH.DiagonalToHPBridge public
open import LogOS.Domain.Opacity.Applications.GRH.DiagonalAdapter public
open import LogOS.Domain.Opacity.Applications.GRH.DiagonalNTemplate public

open import LogOS.Domain.Opacity.Applications.GRH.Systems public
open import LogOS.Domain.Opacity.Applications.GRH.ZFCBridge public
