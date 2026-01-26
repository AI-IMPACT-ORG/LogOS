{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.AssumptionsBundles where

-- Smoke test: the consolidated assumption bundles are importable and usable.

open import LogOS.Prelude
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Packs.Assumptions.All

import LogOS.Domain.UniversalIR.KernelRichG as UIR

core-uir : LogicCore {lzero}
core-uir = coreFromGradedKernel UIR.GUKR

uni-uir : UniversalityBundle core-uir
uni-uir = record { stepGrade = QAdapter.e (LogicCore.Q core-uir) }
