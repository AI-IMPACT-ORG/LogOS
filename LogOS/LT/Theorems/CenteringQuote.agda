{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.CenteringQuote where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Centering/no-fork theorem packaging for guarded quotation.
--
-- The implementation still uses the internal `QuoteConeMMP` family, but the
-- public theorem vocabulary is centred on contractible fibres and no-fork
-- quotation rather than on separate “cone/MMP” narrations.

open import LogOS.Prelude

import LogOS.LT.Theorems.QuoteConeMMP.PreQuotePort as PreQuotePort
import LogOS.LT.Theorems.QuoteConeMMP.QuoteStable as QuoteStable
import LogOS.LT.Theorems.QuoteConeMMP.QuotationConeImpl as QuotationConeImpl
import LogOS.LT.Theorems.QuoteConeMMP.IndexedQuotationConeImpl as IndexedQuotationConeImpl
import LogOS.LT.Theorems.QuoteConeMMP.ClosureKernelMMPImpl as ClosureKernelMMPImpl
import LogOS.LT.Theorems.StableCompletion as StableCompletion
open StableCompletion public using
  ( CompletionLaw
  ; CompletionLaw≈
  ; stableCompletion-noFork
  ; stableCompletion⇒completion
  ; completion⇒stableCompletion
  )

open PreQuotePort public
open QuoteStable public
module CenteredQuote = QuotationConeImpl.QuotationCone
module IndexedCenteredQuote = IndexedQuotationConeImpl.IndexedQuotationCone
module ClosureKernelCentering = ClosureKernelMMPImpl.ClosureKernelMMP
