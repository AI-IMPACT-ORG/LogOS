{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.View.Roles where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Role-tagged wrappers around `View`.
--
-- Internally, a view is just an observation map `μ : X → Con O`.
-- Publicly, many interfaces use views in different semantic roles (decode maps,
-- probe suites, transport observations, program semantics, ...).
--
-- These wrappers are intentionally lightweight: they erase to the same `View`
-- implementation, but make intent visible in types.

open import LogOS.Prelude
import LogOS.LT.View as View

open View public
  using
    ( ViewRole
    ; decodeR
    ; probeR
    ; transportR
    ; obsR
    ; programR
    ; presentationR
    ; RoleView
    ; mkRoleView
    ; V
    ; forget
    ; μᵣ
    ; DecodeView
    ; ProbeView
    ; TransportView
    ; ObsView
    ; ProgramView
    ; PresentationView
    )
