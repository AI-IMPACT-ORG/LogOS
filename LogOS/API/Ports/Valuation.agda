{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.Valuation where

-- Curated port surfaces for valuation/numeric buses.

open import LogOS.Ports.Valuation.QAdapter public
open import LogOS.Ports.Valuation.NatQAdapter public using (natQAdapter; natQClock)
open import LogOS.Ports.Valuation.ScaleBoundary public
open import LogOS.Ports.Valuation.AbstractQuanticNucleus public
open import LogOS.Ports.Valuation.AbstractConnesKreimer public

module QAdapterBus where
  open import LogOS.Ports.Valuation.QAdapterBus public

open import LogOS.Ports.Valuation.QAdapterBudgetTransport public using
  ( QBudgetTransport
  ; QTimeBudgetTransport
  )

module TimeBudget where
  open import LogOS.Ports.Valuation.QAdapterBudgetTransport2Cat public
