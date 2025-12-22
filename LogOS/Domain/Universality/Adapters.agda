{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Adapters where

-- Bridges/adapters for universality: canonical adapter, transport packs,
-- physics/complexity scaffolding, and Flow helpers.

open import LogOS.Domain.Universality.Adapter public

import LogOS.Domain.Universality.RiceTransport as URice
module RiceTransport where
  open URice public

import LogOS.Domain.Universality.BodyEqTransport as UBodyEq
module BodyEqTransport where
  open UBodyEq public

open import LogOS.Domain.Universality.FlowUniversality public
open import LogOS.Domain.Universality.Lemmas public
open import LogOS.Domain.Universality.Complexity public
open import LogOS.Domain.Universality.ComplexitySpectrum public
open import LogOS.Domain.Universality.Physics public
open import LogOS.Domain.Universality.Separation public
open import LogOS.Domain.Universality.Models public
