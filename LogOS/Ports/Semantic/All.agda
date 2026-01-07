{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.All where

-- Full semantic port surface: core interfaces + canonical interlingua theorems.

open import LogOS.Ports.Semantic.Core public
open import LogOS.Ports.Semantic.SatMor public
open import LogOS.Ports.Semantic.InterlinguaCore public
open import LogOS.Ports.Semantic.Interlingua public

module Hetero where
  open import LogOS.Ports.Semantic.HeteroInterlinguaCore public

module IO where
  open import LogOS.Ports.Semantic.ProofTransport public

module Systems where
  open import LogOS.Ports.Semantic.SystemIO public
  open import LogOS.Ports.Semantic.BoundarySystemIO public
