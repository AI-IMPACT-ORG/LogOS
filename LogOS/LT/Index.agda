{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Index where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Reading order / index module for the LT core.
--
-- This module is intentionally light-weight:
-- it does not re-export anything and only exists as a stable anchor for
-- contributors (humans and AI) who want a “start here” path inside `LogOS/LT/**`.
--
-- Suggested reading order (architecture → implementation → law):
--
-- 1. `LogOS.LT.ConPreorder`      (refinement kit: `⊑`, `≈`, monotone maps)
-- 2. `LogOS.LT.View`             (named observations + pullback refinement)
-- 3. `LogOS.LT.Kernel`           (boundary + code + decode)
-- 4. `LogOS.LT.Coherence`        (coherence modes and relation-polymorphic transport)
-- 5. `LogOS.LT.BoundaryHom`      (architecture: boundary transport only)
-- 6. `LogOS.LT.LOG.Boundary2Cat` (architecture: boundary-only base `LOGᴳ`)
-- 7. `LogOS.LT.BoundaryImplementation.Core` (pure implementation witness over boundary transport)
-- 8. `LogOS.LT.LOG.Implementation2Cat.Core` (implementation displayed over `LOGᴳ`)
-- 9. `LogOS.LT.Hom.Core`         (pure façade semantics)
-- 10. `LogOS.LT.LOG.Kernel2Cat`  (stable façade thin 2-category `LOG`)
-- 11. `LogOS.LT.DisplayedThin2Cat` (displayed layers + Σ-totalisation)
-- 12. `LogOS.LT.Ports.PortSig` / `LogOS.LT.Ports.PortStack` (tagging, stacking, capabilities)
--
-- Stable user-facing façade paths remain:
-- - `LogOS.LT.BoundaryImplementation`
-- - `LogOS.LT.LOG.Implementation2Cat`
-- - `LogOS.LT.Hom`
--
-- For “how do I add a port?” see:
-- - `docs/Patterns/HowTo/HowTo_Add_Port.lagda.md`
--
-- For the repository-level taxonomy (spine vs ports vs views vs apps) see:
-- - `docs/Patterns/Content_Placement.lagda.md`
--
-- For the tetrahedral local-refinement architecture reading (packaging only;
-- no new axioms) see:
-- - `LogOS.LT.Architecture.Tetrahedron`
-- - `LogOS.LT.Architecture.BiPyramid` (derived construction/discipline face)
-- - `docs/Core/Architecture/Tetrahedron.lagda.md`
