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
open import LogOS.Ports.Semantic.VacuityGuards public
import LogOS.Ports.Semantic.Interoperability as Interoperabilityₛ
import LogOS.Ports.Semantic.CanonicalPorts as CanonicalPortsₛ

module Interoperability = Interoperabilityₛ
module CanonicalPorts = CanonicalPortsₛ

module Hetero where
  open import LogOS.Ports.Semantic.HeteroInterlinguaCore public

module IO where
  open import LogOS.Ports.Semantic.ProofTransport public

module Systems where
  open import LogOS.Ports.Semantic.SystemIO public
  open import LogOS.Ports.Semantic.BoundarySystemIO public

module StrictReindex where
  open import LogOS.Ports.Semantic.InterlinguaStrictReindex public

module StrictKernel where
  open import LogOS.Ports.Semantic.InterlinguaStrictKernel public

module CodeKernel where
  open import LogOS.Ports.Semantic.InterlinguaCodeKernel public
