{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Empty where

-- Minimal empty type surface (std-lib compatible name).
--
-- Note: the Agda primitive prelude does not ship a `Data.Empty` module under
-- `--no-libraries`. LogOS defines `⊥` and `⊥-elim` in `LogOS.Syntax.Prop`; we
-- re-export that canonical definition here to keep `Data.*` imports lightweight
-- and consistent across the codebase.

open import LogOS.Syntax.Prop public using (⊥; ⊥-elim)
