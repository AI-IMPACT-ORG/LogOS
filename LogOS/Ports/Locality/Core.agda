{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Locality.Core where

-- Dependent-locality injection port (canonical by design for v1.1).
--
-- Canonical-by-design (v1.1) locality injection point: dependent locality as a port,
-- i.e. semantics presented as a family of local probes
-- whose observation preorders may vary with the index.
--
-- Motivation:
-- many “distributed boundary” designs want different local interface shapes at
-- different indices (e.g. archimedean vs non-archimedean places in number
-- theory, or different sensor types in a physical system).
--
-- This module is the canonical-by-design notion of locality in v1.1:
-- local probes → combined observation → pullback refinement,
-- with an index-dependent observation preorder family (`DFunPreorder`).
-- `LocalityPort` is the primitive observation port in this lane.
-- `LogOS.Ports.Realisations.DependentStack` is the generic shared-boundary /
-- many-realisations layer built on top of it.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_)
open import LogOS.LT.FunPreorder using (DFunPreorder)
open import LogOS.LT.View using (View; PullbackPreorder)
open import LogOS.LT.Kernel using (Kernel; kernelFromView)
open import LogOS.LT.Presentation.ObservationInitiality using
  ( DependentProbeSuite
  ; suiteViewᵈ
  ; _⊑⟦_⟧ᵈ_
  )

LocalBoundary
  : ∀ {ℓI ℓOCon ℓORel}
  → (I : Set ℓI)
  → (O : I → ConPreorder ℓOCon ℓORel)
  → ConPreorder (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel)
LocalBoundary I O = DFunPreorder I O

record LocalityPort
  {ℓX ℓI ℓOCon ℓORel : Level}
  (X : Set ℓX)
  (I : Set ℓI)
  (O : I → ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    localProbe : (i : I) → View X (O i)

  suite : DependentProbeSuite X I O
  suite = record { probe = localProbe }

  -- Combined observation as a single view into the dependent pointwise boundary.
  localView : View X (LocalBoundary I O)
  localView = suiteViewᵈ suite

  LocalityPreorder : ConPreorder ℓX (ℓI ⊔ ℓORel)
  LocalityPreorder = PullbackPreorder localView

  infix 4 _⊑loc_ _≈loc_

  _⊑loc_ : X → X → Set (ℓI ⊔ ℓORel)
  x ⊑loc y = x ⊑⟦ suite ⟧ᵈ y

  _≈loc_ : X → X → Set (ℓI ⊔ ℓORel)
  _≈loc_ = _≈_ LocalityPreorder

open LocalityPort public

-- "A dependent local model is a kernel": package a dependent locality port as a kernel.
localKernel
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → LocalityPort X I O
  → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓX
localKernel P =
  kernelFromView (LocalityPort.localView P)
