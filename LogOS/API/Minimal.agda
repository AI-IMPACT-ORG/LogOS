{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Minimal where

-- ============================================================================
-- LogOS API — MINIMAL ENTRY POINT
-- 
-- This module provides the absolute essentials for defining and using LogOS models.
-- Use this when you just need to:
--   - Define a signature
--   - Construct a model
--   - Use basic operations
--
-- This is the canonical `--safe` core API entry in this codebase.
-- Guarantee: this module does not import `LogOS.Axioms.*` (no global postulates).
-- For curated, heavier packs (ZFC/opacity/complexity/universality/IR), import the relevant
-- `LogOS/Packs/*` module directly (no umbrella packs entrypoint).
-- Deprecated “Standard/Full” APIs are not present here. Additional theorems and
-- adapters live under `LogOS.Theorems.*`, `LogOS.Ports.*`, and `LogOS.Adapters.*`.
-- ============================================================================

open import LogOS.Prelude

-- ============================================================================
-- SIGNATURE
-- ============================================================================

-- Core signature: sorts, operations, relations (kept as-is)
open import LogOS.Base.Signature public
open import LogOS.Base.Signature.Hom public

-- ============================================================================
-- MINIMAL CORE (S/H/G with explicit laxness)
open import LogOS.Minimal.Tier      public
open import LogOS.Minimal.Adapter   public
open import LogOS.Minimal.ScaleOps  public
open import LogOS.Minimal.World     public
open import LogOS.Minimal.Con       public
open import LogOS.Minimal.Closure   public
open import LogOS.Minimal.Adjunction public
open import LogOS.Minimal.Truth     public
open import LogOS.Algebra.ConAlg    public
open import LogOS.Free.Constraints  public

-- ============================================================================
-- KERNEL (integrated S/H/G + Code)
open import LogOS.Kernel public
open import LogOS.Kernel.Finite public
open import LogOS.Kernel.Infinite public
open import LogOS.Kernel.Reindex public
open import LogOS.Kernel.HomOverSig public
open import LogOS.Kernel.Infinite.Lemmas public hiding (module For)
open import LogOS.Kernel.Infinite.Hom public
open import LogOS.Kernel.Infinite.Initial public
open import LogOS.Kernel.Infinite.Reindex public
open import LogOS.Kernel.Endo public
open import LogOS.Kernel.TensorDSL public
open import LogOS.Kernel.Hom public
open import LogOS.Kernel.Initial public
open import LogOS.Kernel.Initial.OverSig public
open import LogOS.Ports.All     public
open import LogOS.Adapters.All  public
-- Computation API
open import LogOS.Computation.Core       public
open import LogOS.Computation.FromKernel public
-- Definitions helpers not re-exported to keep API lean
open import LogOS.Computation.Blum       public

-- No separate institutional layer exported; Kernel integrates the views

-- ============================================================================
-- BOUNDARY I/O (swappable) AND BRIDGE
open import LogOS.Boundary.IO         public
open import LogOS.Boundary.MultiIO    public
open import LogOS.Boundary.Semantics  public
open import LogOS.Boundary.Port       public

-- ============================================================================
-- USAGE EXAMPLE
-- ============================================================================
--
--   open import LogOS.API.Minimal
--   
--   -- Define your signature
--   sig : LogOSSignature ℓ
--   sig = record { ... }
--   
--   -- Choose a Quantale+Time adapter (finite-join quantale + time monoid embedding).
--   -- Ready-made instances:
--   --   `LogOS.QAdapters.QNat.QNat`    (steps/time as ℕ, with max/join)
--   --   `LogOS.QAdapters.QNat2.QNat2`  (two-axis budgets: unitary + measurement)
--   --   `LogOS.QAdapters.QNatTop.QNatTop` (ℕ with an explicit top grade ω)
--   Q : QAdapter ℓ
--   Q = LogOS.QAdapters.QNat.QNat
--   
--   -- Provide a single integrated kernel (S/H/G + Code) instance
--   kernel : Kernel sig Q
--   kernel = record
--     { HWorld = ... ; BB = ... ; MBulk = ... ; MBnd = ... ; Holo = ...
--     ; HTruth = ... ; HInv = ...
--     ; Sat_H_bnd = ... ; sat-coh = ...
--     ; Fml = ... ; Strict = ... ; TransH = ... ; coh-LH = ...
--     ; GTruth = ...
--     ; Code = ... ; encode = ... ; decode = ... ; decode∘encode = ...
--     ; Guard = ... ; Body = ... ; guard-decode = ...
--     ; γ* = ... ; γ*-guard = ... ; decode-γ* = ...
--     ; reify = ... ; reify-decode = ...
--     ; Body∂ = ... ; body-decode = ...
--     }
