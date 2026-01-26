{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Empty where

-- Minimal empty type surface (std-lib compatible name).
--
-- LogOS defines `⊥` and `⊥-elim` in `LogOS.Syntax.Prop`; we re-export that
-- canonical definition here to keep the host-wrapper layer lightweight.

open import LogOS.Syntax.Prop public using (⊥; ⊥-elim)

