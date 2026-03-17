{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.All where

-- ZFC application pack (stack-first).
--
-- Goal: present ZF/ZFC as the heavy stack-first application pack whose primary
-- interface is a disciplined deck of logical-transformer layers over one
-- shared set boundary.
--
-- Entrypoints:
-- - `LogOS/Apps/ZFC/All.agda`
-- - `LogOS/Apps/ZFC/Stack.agda`
-- - `LogOS/Apps/ZFC/Proof.agda`
-- - `LogOS/Apps/ZFC/Stack/ReifiedTower.agda`
-- - `LogOS/Apps/ZFC/SetTheory/Definable.agda`
-- - `LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`
-- - guide: `LogOS/Apps/ZFC/README.md`
--
-- Implemented now:
-- - the implemented surfaces are exactly the aliases below
-- - detailed pack narration lives in `LogOS/Apps/ZFC/README.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs

-- Proof-layer surface (syntax + closed axiom formulas).
--
-- Note: we intentionally do *not* re-export `Proof.Semantics` from this
-- entrypoint, to avoid clashing helper names with `SetTheory.Derived`. Import
-- it explicitly when you want the full soundness development.
--
-- Note likewise: the iterative-tree semantic facades
-- (`Models/IterativeSetTree/Semantics*.agda`) and the Metamath bridge
-- (`MetamathSurface.agda`) are imported explicitly when needed, rather than
-- flattened through this top-level pack surface.

import LogOS.Apps.ZFC.Stack
import LogOS.Apps.ZFC.SetTheory.Definable
import LogOS.Apps.ZFC.Proof.Syntax
import LogOS.Apps.ZFC.Proof.Axioms

module Stack = LogOS.Apps.ZFC.Stack
module Definable = LogOS.Apps.ZFC.SetTheory.Definable
module ProofSyntax = LogOS.Apps.ZFC.Proof.Syntax
module ProofAxioms = LogOS.Apps.ZFC.Proof.Axioms
