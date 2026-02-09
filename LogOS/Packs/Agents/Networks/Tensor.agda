{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Tensor where

open import LogOS.Prelude

-- Re-export the kernel’s tensor/endomap DSL: this is the compositional “wiring”
-- language for networked open systems.

open import LogOS.Kernel.TensorDSL public
