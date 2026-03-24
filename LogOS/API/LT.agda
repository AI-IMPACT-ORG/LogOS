{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.LT where

-- Curated navigation surface for the logical-transformer core.
--
-- Intention: downstream work should import from here (or deeper `LogOS/LT/**`)
-- rather than reaching into downstream application packs directly.
-- The typed tetrahedron/face architecture package is part of this default
-- surface; its equality bookkeeping remains quarantined under the explicit
-- `LogOS.LT.Architecture.Definitional` module.
--
-- Refinement-first policy:
-- strictification is intentionally not re-exported from this flat surface.
-- Import `LogOS.API.Strictification` explicitly if a development really needs it.

import LogOS.API.Architecture as Architecture

open import LogOS.API.Core public
open import LogOS.API.Architecture public
open import LogOS.API.Kernel public
open import LogOS.API.Ports public
open import LogOS.API.Stacks public hiding
  ( map∂
  ; map∂-mono
  ; mapCode
  ; decode-mapCode
  ; toKernelHomLike
  ; toKernelHom
  ; fromKernelHomLike
  ; fromKernelHom
  )
open import LogOS.API.Theorems public

open Architecture.Discipline public using
  ( mkTotalObjR
  ; mkTotalHomR
  )

module SuccessorIndex where
  open import LogOS.LT.Stage.SuccessorChain public using
    ( SuccessorChain
    ; next
    ; StageOf
    ; levelChain
    ; Stageω
    ; zero
    ; suc
    ; iterω
    )
