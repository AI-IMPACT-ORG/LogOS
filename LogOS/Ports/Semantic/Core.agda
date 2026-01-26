{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.Core where

-- Semantic “ports” = presentations of a shared boundary satisfaction relation.
--
-- This module provides the minimal interfaces; theorems live in
-- `LogOS.Ports.Semantic.InterlinguaCore` and `LogOS.Ports.Semantic.Interlingua`.

open import LogOS.Prelude

open import LogOS.Boundary.Port public
  using (BoundaryPort; canonicalPort)

open import LogOS.Ports.Semantic.InterlinguaCore public
  using (PresentationC; canonicalPresentation)

open import LogOS.Ports.Semantic.Interlingua public
  using (toPresentationC)

-- More literature-aligned alias names (kept lightweight).

BoundaryPresentation = BoundaryPort
Presentation = PresentationC

