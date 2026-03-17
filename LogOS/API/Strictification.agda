{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Strictification where

-- Explicit strictification surface.
--
-- This module gathers the opt-in paths from refinement/guarded semantics into
-- strict equality, stack-level strict decode laws, and antisymmetry-based
-- collapse. The default curated APIs intentionally do not re-export these names.

module Kernel where
  open import LogOS.LT.Hom.Strictification public

module Architecture where
  open import LogOS.LT.Theorems.ArchitecturalNormalFormStrictification public
  module Faces where
    open import LogOS.LT.LOG.PortReindexing.Strictification public

module View where
  open import LogOS.LT.View.Strictification public

module Institution where
  open import LogOS.LT.InstitutionFragment.Strictification public

module Stack where
  open import LogOS.LT.Stack.Strictification public

module TypeTheory where
  open import LogOS.LT.TypeTheory.Strictification public

module Theorems where
  open import LogOS.API.Theorems.Strictification public

module Ports where
  open import LogOS.Ports.ClassicalLimit public
  open import LogOS.API.Ports.LTStrictificationLOG public
