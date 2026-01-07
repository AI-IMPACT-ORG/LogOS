{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Adapter where

-- Adapter module bundling core imports for Universality examples.

open import LogOS.API.Minimal        public
open import LogOS.Domain.Universality.Core     public
open import LogOS.Domain.Universality.Comp     public
open import LogOS.Domain.Universality.Kernel   public
open import LogOS.Domain.Universality.PAExample public
open import LogOS.Domain.Universality.Complexity public
open import LogOS.Domain.Universality.ComplexitySpectrum public
open import LogOS.Domain.Universality.Physics           public
open import LogOS.Domain.Universality.Separation        public
open import LogOS.Domain.Universality.Growth            public
open import LogOS.Domain.Universality.FlowUniversality public
-- open import Models.Universality.QuantumDemo        public -- keep demos separate to avoid name clashes
-- open import Models.Universality.QuantumInstantiation public
open import LogOS.Domain.Universality.Models            public
