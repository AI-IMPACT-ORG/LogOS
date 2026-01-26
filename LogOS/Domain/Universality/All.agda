{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.All where

-- Canonical “all surfaces” entrypoint for Universality:
-- core + kernel + transports + complexity/physics scaffolding.

-- Domain umbrella: depend on the kernel surface, not the batteries-included API.
-- This keeps `API.Minimal` reserved for kernel-authoring work.
open import LogOS.API.Kernel public
open import LogOS.Domain.Universality.Core public
open import LogOS.Domain.Universality.Comp public
open import LogOS.Domain.Universality.Kernel public
import LogOS.Domain.Universality.KernelRich as KernelRichₜ
module KernelRich = KernelRichₜ
open import LogOS.Domain.Universality.PAExample public
open import LogOS.Domain.Universality.Complexity public
open import LogOS.Domain.Universality.ComplexitySpectrum public
open import LogOS.Domain.Universality.Physics public
open import LogOS.Domain.Universality.Separation public
open import LogOS.Domain.Universality.Growth public
open import LogOS.Domain.Universality.FlowUniversality public
open import LogOS.Domain.Universality.Models public
open import LogOS.Domain.Universality.Lemmas public
open import LogOS.Domain.Universality.SchemePresentation public

import LogOS.Domain.Universality.RiceTransport as URice
module RiceTransport where
  open URice public

import LogOS.Domain.Universality.BodyEqTransport as UBodyEq
module BodyEqTransport where
  open UBodyEq public
