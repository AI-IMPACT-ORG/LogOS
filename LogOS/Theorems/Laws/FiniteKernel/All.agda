{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Laws.FiniteKernel.All where

-- Finite/minimal kernel laws (no ω-chain structure required).

open import LogOS.Theorems.Laws.FiniteKernel.H public
open import LogOS.Theorems.Laws.FiniteKernel.S public
open import LogOS.Theorems.Laws.FiniteKernel.Adapters public
open import LogOS.Theorems.Boundary.Reflection public
open import LogOS.Theorems.Code.Core public
