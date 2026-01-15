{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.RefinementInitiality where

-- UniversalIR-facing initiality: any kernel instantiation over the UniversalIR
-- signature factors through the free kernel up to refinement.

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.KernelRichG using (Sig; Q; GUKR)
open import LogOS.Minimal.World
open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.Initial using (build)
import LogOS.Theorems.CategoryTheory.Kernel2CatInitial as K2Init

HWorld : Worlds.WorldH Sig Q
HWorld = GradedKernel.HWorld GUKR

module InitialRefinement = K2Init.InitialRefinement Sig Q HWorld
open InitialRefinement public
