{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Architecture where

-- ============================================================================
-- LogOS API — ARCHITECTURE MAP
--
-- This surface is for:
-- - navigation (a map of the ports/adapters spine)
-- - port-first downstream imports (`open Architecture.Downstream`)
-- - keeping kernel names out of the default namespace (unless you open `Kernels`)
--
-- Not for:
-- - “import everything” work (prefer targeted surfaces or packs)
-- - curated application entrypoints (use `LogOS.Packs.*.Surface`)
--
-- Canonical navigation surface for the “ports/adapters” spine:
--
--   1) signatures + signature morphisms
--   2) kernels + reindexing (model reduct/view)
--   3) boundary I/O (communicable meaning)
--   4) semantic ports/presentations (import+export legs)
--   5) canonical interlingua translations + uniqueness (up to satisfaction)
--   6) computation/process morphisms (SchemeCategory)
--
-- OO reading (without mutable state): a `Kernel` instance is an
-- “object” (a semantic point exposing interfaces), and ports/adapters are the
-- interface maps and functorial transports between such points.
--
-- This module is intentionally an index: it avoids dumping everything into one
-- namespace; instead it presents the layers as named submodules.
-- ============================================================================

open import LogOS.Prelude public

module Signatures where
  open import LogOS.Base.Signature public
  open import LogOS.Base.Signature.Hom public

-- Kernel authoring surface (kept namespaced to avoid collisions by default).
import LogOS.API.Kernel as Kernelsₐ
module Kernels = Kernelsₐ

module Boundary where
  open import LogOS.Boundary.IO public
  open import LogOS.Boundary.MultiIO public
  open import LogOS.Boundary.Semantics public
  open import LogOS.Boundary.Port public

module Systems where
  -- Boundary-first “open systems”: packaged boundary I/O together with its
  -- ambient signature/world/truth data.
  open import LogOS.System public

module Semantics where
  -- Satisfaction systems (`Ctx/Con/Sat`) and their morphisms.
  --
  -- This is the common currency of the ports/adapters spine.
  open import LogOS.Ports.Semantic.Core public using (SatSystem; satSystem)
  open import LogOS.Ports.Semantic.PresentationCore public using (PresentationC)
  open import LogOS.Ports.Semantic.SatMor public using (SatMor; SatHom; idSatMorS; idSatHomS; composeSatMor; composeSatHom)

module Ports where
  open import LogOS.Ports.Surface public

module Adapters where
  open import LogOS.Adapters.Surface public

module Computation where
  open import LogOS.Computation.SchemeCategory public

module Processes where
  -- Process = state carrier + dynamics + closure + observation + cost algebra.
  open import LogOS.Computation.SchemeCategory public using
    ( Process
    ; processWithCost
    ; ProcessHom
    ; ProcessHomLax
    ; ProcessHomCost
    ; ProcessHom→Lax
    )

module Interfaces where
  -- Interfaces = compilation + fuel (into a shared process), with induced semantics.
  open import LogOS.Computation.SchemeCategory public using
    ( Interface
    ; schemeFromInterface
    ; mapInterface
    ; mapInterfaceLax
    )
  open import LogOS.Ports.Semantic.SchemeCategorySatSystem public using
    ( computesWithinSatSystem
    ; computesWithinSatSystem-map
    )

module CategoryTheory where
  -- Small categorical packaging for ports/presentations.
  open import LogOS.Theorems.CategoryTheory.PortCat public

module Quantitative where
  -- `QAdapter` instances (prequantale + time homomorphism `τ`).
  open import LogOS.QAdapters.All public

module Contracts where
  -- Signature-indexed constraint syntax + renaming along `SigHom`.
  open import LogOS.Minimal.ConstraintsOverSig public

module Tooling where
  -- Proof-carrying “I/O” surfaces for external tools (provers/solvers).
  open import LogOS.Syntax.ProofSystem public
  open import LogOS.Ports.Semantic.ProofTransport public
  open import LogOS.Ports.Semantic.SatSystemIO public

module Downstream where
  -- Port-first “default view” for downstream developments.
  --
  -- Typical usage:
  --   open import LogOS.API.Architecture
  --   open Architecture.Downstream
  --
  -- This keeps kernel names out of the immediate namespace while still giving
  -- access to the ports/adapters spine.
  open Signatures public
  open import LogOS.Minimal.Adapter public using (QAdapter)
  open import LogOS.Minimal.World public
  open import LogOS.Minimal.Con public
  open Boundary public
  open Tooling public
  open Ports public
  open Systems public
  open Processes public
  open Interfaces public

module Assumptions where
  -- Core logic-core bundle (used by pack-level assumption bundles).
  open import LogOS.API.Assumptions public
