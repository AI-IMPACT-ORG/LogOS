{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Surface where

-- Stable port/presentation surface:
-- core satisfaction systems + canonical interlingua translations (+ telemetry).
--
-- Tool-facing I/O surfaces live under `LogOS.API.Architecture.Tooling` and in
-- `LogOS.Ports.All` (power-user umbrella).

open import LogOS.Ports.Semantic.Core public
open import LogOS.Ports.Semantic.SatMor public
open import LogOS.Ports.Semantic.Interlingua public
open import LogOS.Ports.Semantic.VacuityGuards public
open import LogOS.Ports.Semantic.Meaningful public

import LogOS.Ports.Semantic.Interoperability as Interoperabilityₛ
import LogOS.Ports.Semantic.CanonicalPorts as CanonicalPortsₛ
module Interoperability = Interoperabilityₛ
module CanonicalPorts = CanonicalPortsₛ
module Limit = Interoperabilityₛ.Limit

module Hetero where
  open import LogOS.Ports.Semantic.HeteroInterlinguaCore public

open import LogOS.Ports.Telemetry.All public
open import LogOS.Ports.SpectralPack public
