{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.Core where

-- Curated, stable “executable universal logic” surface (no demos).

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

open import LogOS.Prelude

-- Core building blocks (Domain). Keep them namespaced.
import LogOS.Domain.Universality.Core as Domainₜ
module Domain = Domainₜ

-- Stable scheme presentation of the universality core.
module CoreScheme where
  import LogOS.Domain.Universality.SchemePresentation as SP
  import LogOS.Computation.Scheme as Scheme

  runCore : ∀ n u → Domain.CoreUCode
  runCore n u = Scheme.run SP.CoreScheme (SP.mkInput n u)

  runCore-simulate : ∀ n u → runCore n u ≡ Domain.simulateCoreU n u
  runCore-simulate n u = SP.run-simulate n u

-- Kernel/port view of the universality core.
module Ports where
  import LogOS.Domain.Universality.KernelRich as KR
  import LogOS.Ports.Semantic.CanonicalPorts as CP

  -- Note: `KR.UKR` is an observer-shaped kernel for *structure* and
  -- encode/decode/flow wiring; its H-tier truth is intentionally vacuous.
  -- Any non-vacuity/meaningfulness claims must supply separate vacuity guards.

  module KPorts = CP.For KR.UKR
  open KPorts public
