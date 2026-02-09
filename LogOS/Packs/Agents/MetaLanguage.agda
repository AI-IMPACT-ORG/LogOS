{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.MetaLanguage where

-- Agent-facing meta-language surface:
-- reuse the existing polymorphic meta-language, then add the boundary/network
-- tooling typically needed by “agents as open systems”.
--
-- The core agent-theoretic power still lives in the kernel. For convenience:
-- - `LogOS.Kernel.Endo` (monitors/closure steps)
-- - `LogOS.Theorems.Boundary.Reflection` (boundary reflection)
-- - `LogOS.Computation.KernelUniversalProcess` (code↔boundary bridge)

open import LogOS.MetaLanguage.All public

module Ports where
  open import LogOS.Boundary.Port public
  open import LogOS.Boundary.MultiIO public
  open import LogOS.Ports.Semantic.All public

module NetworkOps where
  open import LogOS.Kernel.TensorDSL public

module Networks where
  open import LogOS.Packs.Agents.Networks.Hetero public
  open import LogOS.Packs.Agents.Networks.NetworkAgent public

  module Interop where
    open import LogOS.Packs.Agents.Networks.Interop public

  module MonitorInterop where
    open import LogOS.Packs.Agents.Networks.MonitorInterop public

module FixedPoints where
  open import LogOS.Theorems.Boundary.Kernel.Mu public
