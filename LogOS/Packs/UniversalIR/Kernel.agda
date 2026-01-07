{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Kernel where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.KernelRichG public using (Sig; Q; GUKR)
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded.Boundary as GB
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.MultiIO using (MultiBoundaryIO; defaultMultiBoundaryIOFromBoundaryIO)

-- Curated access to the graded kernel instance over UniversalIR,
-- plus default Boundary IO views.

boundaryIO
  : BoundaryIO Sig Q (GradedKernel.HWorld GUKR) (GradedKernel.BB GUKR) (GradedKernel.HTruth GUKR)
boundaryIO = GB.boundaryIO GUKR

multiBoundaryIO
  : ∀ {Role : Set} → MultiBoundaryIO Role Sig Q (GradedKernel.HWorld GUKR) (GradedKernel.BB GUKR) (GradedKernel.HTruth GUKR)
multiBoundaryIO {Role} =
  defaultMultiBoundaryIOFromBoundaryIO {Role = Role} boundaryIO
