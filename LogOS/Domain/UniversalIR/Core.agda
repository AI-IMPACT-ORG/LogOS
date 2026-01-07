{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core where

-- Core surface: shared datatypes and steppers for UniversalIR.
-- This module re-exports the core submodules and is the recommended import.

open import LogOS.Domain.UniversalIR.Core.Utils public
open import LogOS.Domain.UniversalIR.Core.Minsky public
open import LogOS.Domain.UniversalIR.Core.Lambda public
open import LogOS.Domain.UniversalIR.Core.Ethereum public
open import LogOS.Domain.UniversalIR.Core.QuantumOracle public
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit public
open import LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp public
open import LogOS.Domain.UniversalIR.Core.UCode public
