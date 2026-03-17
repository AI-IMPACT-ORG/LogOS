{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.PortReindexing where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-safe LOG reindexing helpers.
--
-- Equality-based pullback/reindexing along `toLOG` lives in the explicit
-- `LogOS.LT.LOG.PortReindexing.Strictification` lane. This default module keeps
-- only the boundary-preserving kernel projection used by refinement-level
-- architecture code.

open import LogOS.Prelude
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedObj
  ; base
  )
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Thin2Functor using (Thin2Functor)

open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.LOG.Implementation2Cat.Core using (LOGᴳʳ; toLOG)

kernelOfToLOG
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (LOGᴳʳ {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
  → DecoratedObj D
  → Kernel ℓ ℓRel ℓCode
kernelOfToLOG {ℓ} {ℓRel} {ℓCode} {D = D} X =
  Thin2Functor.mapObj (toLOG {ℓ} {ℓRel} {ℓCode})
    (base {D = D} X)
