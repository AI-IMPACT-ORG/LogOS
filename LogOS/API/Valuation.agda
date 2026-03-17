{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Valuation where

-- Curated navigation surface for valuation algebra / numerics.

open import LogOS.API.Ports.Valuation public
open import LogOS.Ports.Valuation.QAdapterBudgetTransport public using
  ( transportGradeCutLe
  ; transportTimeGradeCutLe
  )

-- Optional valuation algebra layers (still refinement-first).
--
-- We expose these under a namespace to avoid polluting the default API surface
-- with generic identifiers (e.g. `step`) that are common in downstream docs.
-- Consumers can use them by opening `LogOS.API.Valuation.Algebra` explicitly.
module Algebra where
  open import LogOS.Ports.Valuation.AbstractJoinPrequantale public
  open import LogOS.Ports.Valuation.EngineeringDimension public
  open import LogOS.Ports.Valuation.AbstractQuanticNucleus public
  open import LogOS.LT.Sup.AbstractGeneratedClosure public
  open import LogOS.Ports.Valuation.AbstractConnesKreimer public
  open import LogOS.Ports.Valuation.DimReg public
  open import LogOS.Ports.Valuation.Regularisation public
