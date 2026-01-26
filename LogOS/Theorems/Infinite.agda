{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Infinite where

-- Curated entrypoint: infinite/limit theorems (requires `InfiniteKernel`).

import LogOS.Theorems.Laws.InfiniteKernel.All as InfiniteKernelₜ

module InfiniteKernel = InfiniteKernelₜ
