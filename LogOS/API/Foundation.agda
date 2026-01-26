{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Foundation where

-- Narrow import surface: foundations only.
--
-- Intended use:
-- - define signatures and minimal interfaces
-- - state kernel-independent theorems over the minimal structures
--
-- This module intentionally does NOT re-export kernels, ports/adapters, or
-- domain/packs developments.

open import LogOS.Prelude public

-- Signatures
open import LogOS.Base.Signature public
open import LogOS.Base.Signature.Hom public

-- Minimal core (weak/lax interfaces)
open import LogOS.Minimal.Tier       public
open import LogOS.Minimal.Adapter    public
open import LogOS.Minimal.ScaleOps   public
open import LogOS.Minimal.World      public
open import LogOS.Minimal.Con        public
open import LogOS.Minimal.Closure    public
open import LogOS.Minimal.Adjunction public
open import LogOS.Minimal.Truth      public
open import LogOS.Minimal.Domain     public
open import LogOS.Minimal.Thin2Cat   public

-- Constraint algebra + free constraints (kernel-authoring adjacent, but not kernel-specific).
open import LogOS.Algebra.ConAlg    public
open import LogOS.Free.Constraints  public

