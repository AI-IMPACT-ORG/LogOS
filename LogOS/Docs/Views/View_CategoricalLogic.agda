{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.View_CategoricalLogic where

-- Documentation view: thin categories from refinement, monoidal structure,
-- and the category of kernels (up to decode).

open import LogOS.Prelude public

import LogOS.Minimal.Con as Con
import LogOS.Minimal.Adjunction as Adj
import LogOS.Algebra.ConAlg as ConAlg
import LogOS.Theorems.CategoryTheory.KernelCat as KernelCat
