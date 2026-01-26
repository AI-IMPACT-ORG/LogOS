{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core where

-- Core surface: shared datatypes and steppers for UniversalIR.
-- This module re-exports the core submodules and is the recommended import.

open import LogOS.Domain.UniversalIR.Core.Utils public
open import LogOS.Domain.UniversalIR.Core.Minsky public hiding (Effect; _⊨_)
open import LogOS.Domain.UniversalIR.Core.Lambda public hiding (Effect; _⊨_)
open import LogOS.Domain.UniversalIR.Core.Ethereum public hiding (Effect; _⊨_)
open import LogOS.Domain.UniversalIR.Core.QuantumOracle public hiding (Effect; _⊨_)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit public hiding (Effect; _⊨_)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp public
open import LogOS.Domain.UniversalIR.Core.UCode public
