{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Views where

-- ============================================================================
-- LogOS API — VIEW SURFACES (DOCUMENTATION-ORIENTED)
--
-- This module is an index surface for the documentation “Views” layer:
-- it re-exports the quoteable theorem bundles and helper modules that the
-- view notes cite, while keeping imports mechanically honest and stable.
--
-- Notes:
-- - No new axioms: this is a re-export surface over existing theorems.
-- - No packs/domains: views should stay about the kernel/ports spine itself.
-- ============================================================================

open import LogOS.Prelude public

-- Keep the kernel/ports map namespaced.
import LogOS.API.Architecture as Architectureₐ
module Architecture = Architectureₐ

-- Kernel authoring / kernel interfaces (namespaced).
import LogOS.API.Kernel as Kernelsₐ
module Kernels = Kernelsₐ

-- Port/presentation/adaptation surfaces (namespaced).
import LogOS.API.PortsAdapters as PortsAdaptersₐ
module PortsAdapters = PortsAdaptersₐ

-- Quoteable theorem bundles used by the view notes.
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheoremsₜ
module ViewTheorems = ViewTheoremsₜ

import LogOS.Theorems.Meta.Views as MetaViewsₜ
module MetaViews = MetaViewsₜ

import LogOS.Theorems.Meta.Bootstrapping as Bootstrappingₜ
module Bootstrapping = Bootstrappingₜ

-- Strict (≡-level) interlingua/kernels, used by the multi-institution view.
import LogOS.Ports.Semantic.InterlinguaStrictReindex as StrictReindexₜ
import LogOS.Ports.Semantic.InterlinguaStrictKernel as InterlinguaStrictKernelₜ
import LogOS.Ports.Semantic.InterlinguaCodeKernel as InterlinguaCodeKernelₜ
import LogOS.Adapters.Views.SatMor as ViewSatMorₜ

module StrictReindex = StrictReindexₜ
module InterlinguaStrictKernel = InterlinguaStrictKernelₜ
module InterlinguaCodeKernel = InterlinguaCodeKernelₜ
module ViewSatMor = ViewSatMorₜ

-- Tool-facing ports: proof-carrying I/O and rebasing.
import LogOS.Ports.Semantic.SatSystemIO as SatSystemIOₜ
import LogOS.Ports.Semantic.BoundarySystemIO as BoundarySystemIOₜ
module SatSystemIO = SatSystemIOₜ
module BoundarySystemIO = BoundarySystemIOₜ

-- Observer-from-Kernel derived facts used by the observer-semantics view.
import LogOS.Theorems.Meta.ObserverFromKernel as ObserverFromKernelₜ
module ObserverFromKernel = ObserverFromKernelₜ

-- Topos-shaped view: adjunction/nucleus/sheaf vocabulary.
import LogOS.Theorems.CategoryTheory.AdjunctionMonads as AdjunctionMonadsₜ
import LogOS.Theorems.CategoryTheory.BeckChevalley as BeckChevalleyₜ
import LogOS.Theorems.Reflection.ForcingSheaves as ForcingSheavesₜ
import LogOS.Theorems.Reflection.NucleusMu as NucleusMuₜ

module AdjunctionMonads = AdjunctionMonadsₜ
module BeckChevalley = BeckChevalleyₜ
module ForcingSheaves = ForcingSheavesₜ
module NucleusMu = NucleusMuₜ
