{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.FiniteGraph where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Algebra.Ring
open import LogOS.Algebra.End

record FiniteGraph {ℓ : Level} (R : Ring {ℓ}) : Set (lsuc ℓ) where
  field
    V    : Set ℓ
    EndV : End R V
    A    : End.Mat EndV
    q    : Ring.Carrier R
    r    : ℕ

open FiniteGraph public
