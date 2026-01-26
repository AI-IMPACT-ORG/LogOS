{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.AssumptionsSeparation where

-- Smoke test: the Packs-level separation witnesses compile.

open import LogOS.Packs.Assumptions.Separation as Sep

open Sep.Examples public using (meaningfulUni-notPhys; meaningfulPhys-notUni)

