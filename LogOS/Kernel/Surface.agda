{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Surface where

-- Stable, kernel-centric surface (definitions + standard kernel tooling).
--
-- For “power user” re-exports (finite/infinite interfaces, extra lemmas), see
-- `LogOS.Kernel.All`.

open import LogOS.Kernel public
open import LogOS.Kernel.TierCategorical public
open import LogOS.Kernel.Reindex public
open import LogOS.Kernel.HomOverSig public
open import LogOS.Kernel.Endo public
open import LogOS.Kernel.TensorDSL public
open import LogOS.Kernel.Hom public
