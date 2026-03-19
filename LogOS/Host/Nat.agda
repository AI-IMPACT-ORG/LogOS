{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Nat where

-- Host wrapper around Agda.Builtin.Nat (ℕ).
--
-- This keeps the `ℕ` name across the codebase while avoiding duplicate BUILTIN bindings.
-- Refinement-first note: this wrapper intentionally does not re-export builtin
-- decidable equality `_==_`; equality-sensitive reasoning is kept explicit in
-- higher layers via refinement interfaces.

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _-_; _*_; _<_)
  renaming (Nat to ℕ)
