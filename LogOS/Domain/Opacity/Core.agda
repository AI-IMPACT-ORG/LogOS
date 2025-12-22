{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Core where

-- Core re-exports for the Opacity strand.
--
-- Design intent:
-- - Theorems here are conditional: analytic/physical content is always explicit in record fields.
-- - This strand is application-agnostic: concrete targets like GRH are exported separately.
-- - Keep application-facing wrappers out of the curated surface; expose them under
--   `LogOS.Domain.Opacity.Applications.*`.

open import LogOS.Domain.Opacity.Meaningfulness public
open import LogOS.Domain.Opacity.GRH public

open import LogOS.Domain.Opacity.WeilPositivityBridge public
open import LogOS.Domain.Opacity.WeilCriterionLedger public hiding (WeilCriterion; WeilCriterionWeak)
open import LogOS.Domain.Opacity.WeilCriterionDagger public
open import LogOS.Domain.Opacity.ZetaTruthLedger public hiding (RH_from_AxiomLedger)
open import LogOS.Domain.Opacity.ObservableSector public

open import LogOS.Domain.Opacity.AccessibleWeilLedger public
open import LogOS.Domain.Opacity.AccessibleWeilLimitBridge public
open import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridge public
open import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable public
open import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal public
open import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedger public
open import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedgerStable public

open import LogOS.Domain.Opacity.HasseObservableClass public
open import LogOS.Domain.Opacity.HasseYonedaTransport public
open import LogOS.Domain.Opacity.ZetaHasseYonedaLedger public

open import LogOS.Domain.Opacity.LogicLanglands public
