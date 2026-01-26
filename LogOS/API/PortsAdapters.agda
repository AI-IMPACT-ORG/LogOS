{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.PortsAdapters where

-- Narrow import surface: ports + adapters + boundary I/O.
--
-- Intended use:
-- - port-first downstream developments (presentation/translation)
-- - interoperability and tool-facing interfaces
--
-- This module intentionally does NOT re-export the kernel implementation
-- universe; import `LogOS.API.Kernel` if you need kernels explicitly.

open import LogOS.API.Foundation public

-- Boundary I/O and semantic bridge
open import LogOS.Boundary.IO         public
open import LogOS.Boundary.MultiIO    public
open import LogOS.Boundary.Semantics  public
open import LogOS.Boundary.Port       public

open import LogOS.Ports.All    public
open import LogOS.Adapters.All public

