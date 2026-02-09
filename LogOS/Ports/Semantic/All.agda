{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.All where

-- Full semantic port surface: core interfaces + canonical interlingua theorems.

open import LogOS.Ports.Semantic.Core public
open import LogOS.Ports.Semantic.SatMor public
open import LogOS.Ports.Semantic.Interlingua public
open import LogOS.Ports.Semantic.VacuityGuards public
import LogOS.Ports.Semantic.Interoperability as Interoperabilityₛ
import LogOS.Ports.Semantic.CanonicalPorts as CanonicalPortsₛ

module Interoperability = Interoperabilityₛ
module CanonicalPorts = CanonicalPortsₛ

-- Limit/stabilisation transport (μ-level) lives in the interoperability spine.
module Limit = Interoperabilityₛ.Limit

module Hetero where
  open import LogOS.Ports.Semantic.HeteroInterlinguaCore public

module IO where
  open import LogOS.Ports.Semantic.ProofTransport public

module Tooling where
  open import LogOS.Ports.Semantic.SatSystemIO public
  open import LogOS.Ports.Semantic.BoundarySystemIO public

module StrictReindex where
  open import LogOS.Ports.Semantic.InterlinguaStrictReindex public

module StrictKernel where
  open import LogOS.Ports.Semantic.InterlinguaStrictKernel public

module CodeKernel where
  open import LogOS.Ports.Semantic.InterlinguaCodeKernel public

module KernelLayer where
  open import LogOS.Ports.Semantic.InterlinguaKernelLayer public

module SignaturePushoutHub where
  open import LogOS.Ports.Semantic.SignaturePushoutHub public
