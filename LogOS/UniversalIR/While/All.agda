{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.While.All where

import LogOS.UniversalIR.While.Language as Languageₜ
import LogOS.UniversalIR.While.Typing as Typingₜ
import LogOS.UniversalIR.While.SmallStep as SmallStepₜ
import LogOS.UniversalIR.While.Semantics as Semanticsₜ
import LogOS.UniversalIR.While.Compile as Compileₜ
import LogOS.UniversalIR.While.Decompile as Decompileₜ
import LogOS.UniversalIR.While.Theorems as Theoremsₜ

module Language = Languageₜ
module Typing = Typingₜ
module SmallStep = SmallStepₜ
module Semantics = Semanticsₜ
module Compile = Compileₜ
module Decompile = Decompileₜ
module Theorems = Theoremsₜ

