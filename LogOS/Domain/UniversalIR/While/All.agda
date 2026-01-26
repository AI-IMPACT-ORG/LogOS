{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.All where

import LogOS.Domain.UniversalIR.While.Language as Languageₜ
import LogOS.Domain.UniversalIR.While.Typing as Typingₜ
import LogOS.Domain.UniversalIR.While.SmallStep as SmallStepₜ
import LogOS.Domain.UniversalIR.While.Semantics as Semanticsₜ
import LogOS.Domain.UniversalIR.While.Compile as Compileₜ
import LogOS.Domain.UniversalIR.While.Decompile as Decompileₜ
import LogOS.Domain.UniversalIR.While.Theorems as Theoremsₜ

module Language = Languageₜ
module Typing = Typingₜ
module SmallStep = SmallStepₜ
module Semantics = Semanticsₜ
module Compile = Compileₜ
module Decompile = Decompileₜ
module Theorems = Theoremsₜ

