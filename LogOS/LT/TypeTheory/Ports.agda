{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Ports where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Shallow port authoring helpers.
--
-- This module re-exports the canonical singleton templates under a “TT view”
-- name: they remain the single source of truth for law-ports and Σ-totalisation
-- packaging.

import LogOS.LT.Ports.Template.Singleton2Cat as Singleton2Cat
import LogOS.LT.Ports.Template.LawSingleton2Cat as LawSingleton2Cat

open Singleton2Cat public using (Singleton2Cat)
open LawSingleton2Cat public using (lawPortSig; lawSingleton2Cat)

