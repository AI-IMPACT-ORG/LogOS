{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Infinite where

-- Curated entrypoint: infinite/limit theorems (requires `InfiniteKernel`).

import LogOS.Theorems.Laws.InfiniteKernel.All as InfiniteKernelₜ

module InfiniteKernel = InfiniteKernelₜ
