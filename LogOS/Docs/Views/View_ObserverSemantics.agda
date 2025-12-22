{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.View_ObserverSemantics where

-- Documentation view: observer/physical reading, aligned with the process DSL
-- and the resource/observability interfaces.

open import LogOS.Prelude public
import LogOS.Kernel as Kernel
import LogOS.Kernel.TensorDSL as TensorDSL

import LogOS.Domain.Complexity.ObservabilityBudgetG as ObservabilityBudget
import LogOS.Domain.Complexity.ResourceSchemaG as ResourceSchema
import LogOS.Domain.Universality.NonUnitaryCapacity as NonUnitaryCapacity
import LogOS.Domain.Universality.DataProcessingInequality as DPI

import LogOS.Domain.UniversalIR.Core.QuantumCircuit as QuantumCircuit
