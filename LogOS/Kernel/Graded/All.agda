{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.All where

-- Public graded surface: kernel + endo/hom DSL (no theorems).
--
-- Note: keeping `Kernel/*` free of `Theorems/*` imports preserves a clean
-- layering: `Theorems` depends on `Kernel`, not vice versa. If you want a
-- “batteries included” graded bundle, import `LogOS.Theorems.Boundary.Graded.All`
-- explicitly (or via a pack/model entrypoint).

open import LogOS.Kernel.Graded public
open import LogOS.Kernel.FromGradedKernel public
open import LogOS.Kernel.Graded.Endo public
open import LogOS.Kernel.Graded.Infinite public
open import LogOS.Kernel.Graded.Hom public
open import LogOS.Kernel.Graded.Hom2Cat public
open import LogOS.Kernel.Graded.Reachability public

import LogOS.Kernel.Graded.Tiers as Tiersₜ
module Tiers = Tiersₜ
