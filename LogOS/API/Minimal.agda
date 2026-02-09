{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Minimal where

-- ============================================================================
-- LogOS API — MINIMAL ENTRY POINT
-- 
-- This module is the minimal kernel-authoring entrypoint:
-- it re-exports the foundations, kernels, and kernel-derived computation.
--
-- This is a canonical `--safe` core API entry in this codebase.
-- Guarantee: this module does not import `LogOS.Axioms.*` (no global postulates).
-- For curated, heavier packs (ZFC/opacity/complexity/universality/IR), import
-- the relevant `LogOS/Packs/*` surface.
-- ============================================================================
--
-- Notes on import surfaces:
-- - Kernel authoring: `LogOS/API/Minimal.agda` (this module) or `LogOS/API/Kernel.agda`.
-- - Port-first downstream work: `LogOS/API/PortsAdapters.agda` or `LogOS/API/Architecture.agda`.
-- - Foundations only: `LogOS/API/Foundation.agda`.
--
-- Not for:
-- - axiom-driven strengthenings (use `LogOS.API.Axioms` / `LogOS.API.Strengthenings`)
-- - curated application packs (use `LogOS.Packs.*.Surface`)

open import LogOS.API.Foundation public
open import LogOS.API.Kernel public

-- Kernel-derived computation surface.
open import LogOS.Computation.Core       public
open import LogOS.Computation.FromKernel public
open import LogOS.Computation.Blum       public

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
--   -- Choose a Prequantale+Time adapter (finite-join prequantale + time monoid homomorphism into `Scale`).
--   -- Ready-made instances:
--   --   `LogOS.QAdapters.QNat.QNat`    (steps/time as ℕ, with max/join)
--   --   `LogOS.QAdapters.QNat2.QNat2`  (two-axis budgets: unitary + measurement)
--   --   `LogOS.QAdapters.QNatTop.QNatTop` (ℕ with an explicit top grade ω; budget readout is conventional)
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
