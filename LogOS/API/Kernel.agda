{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Kernel where

-- Narrow import surface: kernels and kernel-level tooling.
--
-- Intended use:
-- - define kernels and kernel morphisms
-- - use kernel-integrated views (finite/infinite/graded interfaces)
--
-- This module intentionally does NOT re-export ports/adapters or domain/packs.

open import LogOS.API.Foundation public

open import LogOS.Kernel public
open import LogOS.Kernel.Finite public
open import LogOS.Kernel.Infinite public
open import LogOS.Kernel.Reindex public
open import LogOS.Kernel.HomOverSig public
open import LogOS.Kernel.Infinite.Lemmas public hiding (module For)
open import LogOS.Kernel.Infinite.Hom public
open import LogOS.Kernel.Infinite.Initial public
open import LogOS.Kernel.Infinite.Reindex public
open import LogOS.Kernel.Endo public
open import LogOS.Kernel.TensorDSL public
open import LogOS.Kernel.Hom public
open import LogOS.Kernel.Initial public
open import LogOS.Kernel.Initial.OverSig public

