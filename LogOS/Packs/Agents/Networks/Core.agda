{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Core where

open import LogOS.Prelude

-- Agent networks are expressed using existing open-system primitives:
-- - role-indexed boundary views (`MultiBoundaryIO`)
-- - heterogeneous wiring via satisfaction morphisms (`SatMor`)
-- - the kernel tensor/endomap DSL for compositional wiring

module Boundary where
  open import LogOS.Boundary.MultiIO public

module TensorDSL where
  open import LogOS.Kernel.LogicKernel.TensorDSL public

module Hetero where
  open import LogOS.Packs.Agents.Networks.Hetero public

module NetworkAgent where
  open import LogOS.Packs.Agents.Networks.NetworkAgent public

module Interop where
  open import LogOS.Packs.Agents.Networks.Interop public

module MonitorInterop where
  open import LogOS.Packs.Agents.Networks.MonitorInterop public
