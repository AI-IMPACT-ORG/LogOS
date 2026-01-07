{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Core where

-- Curated entrypoint: core, assumption-light theorems for the minimal kernel.

import LogOS.Theorems.Laws.FiniteKernel.All as FiniteKernelₜ
import LogOS.Theorems.Boundary.All as Boundaryₜ
import LogOS.Theorems.Code.All as Codeₜ

module FiniteKernel = FiniteKernelₜ
module Boundary = Boundaryₜ
module Code = Codeₜ
