{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.WFGraph.Structure where

open import LogOS.Prelude

open import LogOS.ZFC.SetU.WFGraphCore using (WFGraph)
open import LogOS.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.ZFC.WFGraph.Model
  using (ExtensionalityStructure; PowersetStructure; FoundationStructure)

-- Bundle the carrier structures needed to build the WF-graph set universe.
-- Keeping this in one record avoids “threading five arguments everywhere” and
-- makes dependencies explicit in downstream code.

record WFGraphStructure (ℓ : Level) : Set (lsuc ℓ) where
  field
    G   : WFGraph ℓ
    S   : SupStructure G
    Ext : ExtensionalityStructure G
    P   : PowersetStructure G S
    Fnd : FoundationStructure G
