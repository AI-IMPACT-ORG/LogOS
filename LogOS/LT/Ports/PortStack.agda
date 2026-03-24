{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Uniqueness-first public facade for stacked ports.
--
-- The raw duplicate-tag, leftmost-resolution machinery now lives in the
-- explicit `LogOS.LT.Ports.PortStack.Raw` lane. This facade exports only
-- the public uniqueness discipline and the no-dup witness type needed by it.

import LogOS.LT.Ports.PortStack.Laws as Laws
import LogOS.LT.Ports.PortStack.Coherence as Coherence
import LogOS.LT.Ports.PortStack.Raw as Shadowing
import LogOS.LT.Ports.PortStack.Unique as Unique
open Shadowing public using (NoDupStack)
open Laws public
open Coherence public
open Unique public using
  ( UniquePort
  ; mkUniquePort
  ; UniquePortStack
  ; mkUniquePortStack
  ; uniqueHasPort
  ; uniqueMember
  ; noDupSingleton
  ; singletonUniqueStack
  ; noDupCons
  )

module UniqueInstances where
  open Unique.UniqueInstances public
