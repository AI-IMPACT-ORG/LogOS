{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.View_CurryHowardLambek where

-- Typechecked “view surface” for the Curry-Howard-Lambek presentation.
--
-- Keep this module lightweight to avoid name clashes when imported alongside
-- other views/tests.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
open import LogOS.Theorems.Meta.CHL

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = ViewTheorems.For K
  open V.CHL public
