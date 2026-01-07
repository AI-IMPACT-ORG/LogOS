{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Architecture where

-- ============================================================================
-- LogOS API — ARCHITECTURE MAP
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
-- OO reading (without mutable state): a `Kernel`/`LogicKernel` instance is an
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

module Kernels where
  open import LogOS.Kernel public
  open import LogOS.Kernel.Reindex public
  open import LogOS.Kernel.HomOverSig public

module Boundary where
  open import LogOS.Boundary.IO public
  open import LogOS.Boundary.MultiIO public
  open import LogOS.Boundary.Semantics public
  open import LogOS.Boundary.Port public

module Ports where
  open import LogOS.Ports.Semantic.All public

module Adapters where
  open import LogOS.Adapters.Views.All public

module Computation where
  open import LogOS.Computation.SchemeCategory public

module CategoryTheory where
  -- Small categorical packaging for ports/presentations.
  open import LogOS.Theorems.CategoryTheory.PortCat public

module Quantitative where
  -- `QAdapter` instances (quantale + time embedding).
  open import LogOS.QAdapters.All public

module Contracts where
  -- Signature-indexed constraint syntax + renaming along `SigHom`.
  open import LogOS.Free.ConstraintsOverSig public

module Tooling where
  -- Proof-carrying “I/O” surfaces for external tools (provers/solvers).
  open import LogOS.Syntax.ProofSystem public
  open import LogOS.Ports.Semantic.ProofTransport public
  open import LogOS.Ports.Semantic.SystemIO public
