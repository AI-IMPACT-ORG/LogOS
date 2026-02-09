{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Syntax where

open import LogOS.Packs.Agents.Emit.Backends.Python.Backend using (pythonBackend)
import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.SyntaxCore as SyntaxCore
open SyntaxCore.For pythonBackend public
