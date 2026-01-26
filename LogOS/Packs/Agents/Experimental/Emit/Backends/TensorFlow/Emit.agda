{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Emit where

open import LogOS.Packs.Agents.Emit.Backends.Python.Backend using (pythonBackend)
open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types using (TFEmitSpec)
import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types as Types
import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.EmitCore as EmitCore
open EmitCore.For pythonBackend public

defaultSpec : TFEmitSpec
defaultSpec = Types.defaultSpec
