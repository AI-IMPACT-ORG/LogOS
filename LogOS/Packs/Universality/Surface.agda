{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.Surface where

-- Surface lock for the universality + UniversalIR storyline (executable universal logic):
-- re-export curated pack entrypoints plus the paper-facing IR/language modules.

-- This surface intentionally keeps the two universality developments namespaced:
-- both the lightweight core sketch and the UniversalIR-first story define common
-- names like `iter`, `stepE`, and `gas`.

open import LogOS.Packs.Universality.All public

-- The umbrella `All` pack keeps `UniversalIR` and `Core` namespaced already.
-- This surface adds a small amount of extra, paper-facing convenience.

module ComputationTools where
  open import LogOS.Computation.SchemeCategory public
  open import LogOS.Computation.KernelUniversalProcess public
