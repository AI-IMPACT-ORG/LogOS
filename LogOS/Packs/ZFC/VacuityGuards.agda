{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.VacuityGuards where

-- Non-vacuity witnesses for membership-graph semantics: at least one edge and
-- distinct nodes exist.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.ZFC.WFGraph.Structure using (WFGraphStructure)
open import LogOS.ZFC.SetU.WFGraphCore using (WFGraph)

record WFGraphVacuityGuards {ℓ : Level} (W : WFGraphStructure ℓ) : Set (lsuc ℓ) where
  open WFGraphStructure W
  open WFGraph G
  field
    x y : Node
    x≢y : ¬ (x ≡ y)
    edge : Edge x y
