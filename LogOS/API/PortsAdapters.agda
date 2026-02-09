{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.PortsAdapters where

-- Narrow import surface: ports + adapters + boundary I/O.
--
-- This surface is for:
-- - port-first downstream developments (presentation/translation)
-- - interoperability and tool-facing interfaces
--
-- Not for:
-- - kernel authoring (use `LogOS.API.Minimal` / `LogOS.API.Kernel`)
-- - curated applications (use `LogOS.Packs.*.Surface`)
--
-- This module intentionally does NOT re-export the kernel implementation
-- universe; import `LogOS.API.Kernel` if you need kernels explicitly.

open import LogOS.API.Foundation public

-- Boundary I/O and semantic bridge
open import LogOS.Boundary.IO         public
open import LogOS.Boundary.MultiIO    public
open import LogOS.Boundary.Semantics  public
open import LogOS.Boundary.Port       public
open import LogOS.System              public

open import LogOS.Ports.Surface    public
open import LogOS.Adapters.Surface public
