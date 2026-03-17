{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.QuoteConeMMP where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Internal packaging for guarded quotation results.
--
-- Exported here:
-- - `PreQuotePort` records the one-sided quotation law.
-- - `QuoteStable` packages the stable-point result.
-- - `QuotationCone`, `IndexedQuotationCone`, and `ClosureKernelMMP` package the
--   centering/no-fork consequences.
--
-- Not part of the public theorem vocabulary:
-- downstream docs and APIs should prefer
-- `LogOS.LT.Theorems.CenteringQuote`, which presents the same results without
-- exposing the older quote/cone/MMP packaging name.

open import LogOS.Prelude
import LogOS.LT.Theorems.QuoteConeMMP.PreQuotePort as PreQuotePort
import LogOS.LT.Theorems.QuoteConeMMP.QuoteStable as QuoteStable

import LogOS.LT.Theorems.QuoteConeMMP.QuotationConeImpl as QuotationConeImpl
import LogOS.LT.Theorems.QuoteConeMMP.IndexedQuotationConeImpl as IndexedQuotationConeImpl
import LogOS.LT.Theorems.QuoteConeMMP.ClosureKernelMMPImpl as ClosureKernelMMPImpl

open PreQuotePort public
open QuoteStable public

module QuotationCone = QuotationConeImpl.QuotationCone
module IndexedQuotationCone = IndexedQuotationConeImpl.IndexedQuotationCone
module ClosureKernelMMP = ClosureKernelMMPImpl.ClosureKernelMMP
