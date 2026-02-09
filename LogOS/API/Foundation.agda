{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Foundation where

-- Narrow import surface: foundations only.
--
-- This surface is for:
-- - define signatures and minimal interfaces
-- - state kernel-independent theorems over the minimal structures
--
-- Not for:
-- - kernel authoring (use `LogOS.API.Kernel` / `LogOS.API.Minimal`)
-- - ports/adapters (use `LogOS.API.PortsAdapters` / `LogOS.API.Architecture`)
-- - curated applications (use `LogOS.Packs.*.Surface`)
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
open import LogOS.Minimal.RelPreorder public
open import LogOS.Minimal.View       public
open import LogOS.Minimal.Closure    public
open import LogOS.Minimal.Adjunction public
open import LogOS.Minimal.Truth      public
open import LogOS.Minimal.Domain     public
open import LogOS.Minimal.Thin2Cat   public
open import LogOS.Minimal.RelThin2Cat public hiding
  ( comp-mono
  ; whisker-left
  ; whisker-right
  )

-- Constraint algebra + free constraints (kernel-authoring adjacent, but not kernel-specific).
open import LogOS.Minimal.ConAlg    public
open import LogOS.Minimal.Constraints  public
