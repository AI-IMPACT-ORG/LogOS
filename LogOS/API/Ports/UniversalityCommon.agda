{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.UniversalityCommon where

-- Common curated universality port surface shared by the architecture-first
-- and LOG-based routes.
--
-- Use this module for lower-rung port vocabulary.
-- App-side flagship surface:
-- `LogOS/Apps/Universality/Architecture.agda`

open import LogOS.Ports.Universality.Task public
open import LogOS.Ports.Universality.Core public
open import LogOS.Ports.Universality.CTD.Core public using (FlowSimulationFamily)
open import LogOS.Ports.Universality.CTD.Ledger public using (CTDLedger)
open import LogOS.Ports.Universality.Observation public using
  ( ObservationPort
  ; kernelResultPort
  )
open import LogOS.Ports.Universality.Budget public
open import LogOS.Ports.Universality.Fidelity public
open import LogOS.Ports.Universality.Agreement public
