{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Syntax where

open import LogOS.Packs.Agents.Emit.Backends.Python.Backend using (pythonBackend)
import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.SyntaxCore as SyntaxCore
open SyntaxCore.For pythonBackend public
