{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Axioms where

-- Explicit import surface for *axiom interfaces* (optional strengthenings).
--
-- This surface is for:
-- - explicitly-imported axiom interfaces (optional strengthenings)
--
-- Not for:
-- - the minimal safe core (`LogOS.API.Minimal` stays axiom-free)
--
-- Policy:
-- - `LogOS.API.Minimal` stays axiom-free.
-- - If you want ω-sup/limit reasoning, import the relevant interface from here.

open import LogOS.Prelude public

module OmegaSup where
  open import LogOS.Axioms.OmegaSup.Interface public
