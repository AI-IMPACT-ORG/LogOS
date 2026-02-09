{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.AssumptionsSeparation where

-- Smoke test: the Packs-level separation witnesses compile.

open import LogOS.Packs.Assumptions.Separation as Sep

open Sep.Examples public using (meaningfulUni-notPhys; meaningfulPhys-notUni)

