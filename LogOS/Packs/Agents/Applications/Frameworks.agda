{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Applications.Frameworks where

-- Curated “agent frameworks” application surface:
-- kernel-native frameworks + task-level interfaces.

open import LogOS.Packs.Agents.Frameworks.Core public
open import LogOS.Packs.Agents.Frameworks.KernelNative public
open import LogOS.Packs.Agents.Frameworks.PATask public
open import LogOS.Packs.Agents.Frameworks.PATaskAgreement public
open import LogOS.Packs.Agents.Frameworks.UniversalIR public

