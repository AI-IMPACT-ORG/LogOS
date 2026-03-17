{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Intensional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Intensional/public discipline helpers.
--
-- This module does not change any LT semantics. It provides:
-- - role-tagged view wrappers (human-factor separation of semantic intent),
-- - polarity-safe refinement vocabulary (to reduce `_⊑_` direction mistakes).

import LogOS.LT.View.Roles as Roles
import LogOS.Prelude.Refinement as Refinement

open Roles public
open Refinement.Polarity public
