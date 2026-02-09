{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Universality.Surface where

-- Canonical “all surfaces” entrypoint for Universality:
-- core + kernel + transports + complexity/physics scaffolding.
--
-- For a lightweight index (namespaced), see `LogOS.Universality.All`.

-- Domain umbrella: depend on the kernel surface, not the batteries-included API.
-- This keeps `API.Minimal` reserved for kernel-authoring work.
open import LogOS.API.Kernel public
open import LogOS.Universality.Core public
open import LogOS.Universality.Comp public
open import LogOS.Universality.Kernel public
import LogOS.Universality.KernelRich as KernelRichₜ
module KernelRich = KernelRichₜ
open import LogOS.Universality.PAExample public
open import LogOS.Universality.Complexity public
open import LogOS.Universality.ComplexitySpectrum public
open import LogOS.Universality.Physics public
open import LogOS.Universality.Separation public
open import LogOS.Universality.Growth public
open import LogOS.Universality.FlowUniversality public
open import LogOS.Universality.Models public
open import LogOS.Universality.Lemmas public
open import LogOS.Universality.SchemePresentation public

import LogOS.Universality.RiceTransport as URice
module RiceTransport where
  open URice public

import LogOS.Universality.BodyEqTransport as UBodyEq
module BodyEqTransport where
  open UBodyEq public

