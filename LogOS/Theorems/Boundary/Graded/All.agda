{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.All where

-- Boundary-facing theorems for graded kernels: fixed points, continuity,
-- μ-induction wrappers, and boundary observation/reflection utilities.

open import LogOS.Theorems.Boundary.Graded.Reflection public
open import LogOS.Theorems.Boundary.Graded.Mu public
open import LogOS.Theorems.Boundary.Graded.Continuity public
open import LogOS.Theorems.Boundary.Graded.Guarded public
open import LogOS.Theorems.Boundary.Graded.QuickWins public
