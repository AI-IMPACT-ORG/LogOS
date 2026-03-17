{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.DependentProbeSuiteRepresentation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Representation theorem (dependent probe suites / distributed views).
--
-- A dependent “stack of probes” into varying local interfaces `O i`,
--
--   probe : (i : I) → View X (O i)
--
-- is μ-equivalent (pointwise on observation) to a single view into the
-- dependent distributed boundary:
--
--   View X (DFunPreorder I O)   ≃μ   DependentProbeSuite X I O.
--
-- Readings:
-- - “many local probes” ↔ “one combined distributed view”, without committing
--   to any record/function extensionality principle.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _≈_; ≈-refl)
open import LogOS.LT.FunPreorder using (DFunPreorder)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; kernelFromView)
open import LogOS.LT.Presentation.ObservationInitiality using
  ( DependentProbeSuite
  ; probe
  ; suiteViewᵈ
  )

-- μ-level equivalence packaging (no record/function extensionality assumptions).
--
-- This is the intended meaning of “equivalent” in this module: the two
-- presentations compute observationally equivalent boundary values, pointwise.
record DependentProbeSuiteViewEquiv
  {ℓX ℓI ℓOCon ℓORel : Level}
  (X : Set ℓX) (I : Set ℓI) (O : I → ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    toSuite : View X (DFunPreorder I O) → DependentProbeSuite X I O
    toView  : DependentProbeSuite X I O → View X (DFunPreorder I O)

    μ-toView-toSuite
      : ∀ (V : View X (DFunPreorder I O)) (x : X) (i : I)
      → _≈_ (O i) (μ (toView (toSuite V)) x i) (μ V x i)

    μ-toSuite-toView
      : ∀ (S : DependentProbeSuite X I O) (i : I) (x : X)
      → _≈_ (O i) (μ (probe (toSuite (toView S)) i) x) (μ (probe S i) x)

-- View → DependentProbeSuite (split a distributed observation into its local probes).
dependentProbeSuiteOfView
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → View X (DFunPreorder I O)
  → DependentProbeSuite X I O
dependentProbeSuiteOfView {I = I} {O = O} V =
  record { probe = λ i → record { μ = λ x → μ V x i } }

-- DependentProbeSuite → View (bundle all probes into one distributed observation).
--
-- This is `suiteViewᵈ` from `ObservationInitiality`, re-exposed under a
-- “representation theorem” name.
viewOfDependentProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → DependentProbeSuite X I O
  → View X (DFunPreorder I O)
viewOfDependentProbeSuite = suiteViewᵈ

-- Round-trip laws (pointwise on observations).
--
-- We state these as pointwise mutual refinements of `μ`, rather than equality of `View`
-- records (to avoid committing to a particular extensionality principle for records).

viewOfDependentProbeSuite∘dependentProbeSuiteOfView
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
    (V : View X (DFunPreorder I O))
  → ∀ x i
  → _≈_ (O i)
      (μ (viewOfDependentProbeSuite (dependentProbeSuiteOfView {O = O} V)) x i)
      (μ V x i)
viewOfDependentProbeSuite∘dependentProbeSuiteOfView {O = O} V x i =
  ≈-refl (O i) (μ V x i)

dependentProbeSuiteOfView∘viewOfDependentProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
    (S : DependentProbeSuite X I O)
  → ∀ i x
  → _≈_ (O i)
      (μ (probe (dependentProbeSuiteOfView {O = O} (viewOfDependentProbeSuite S)) i) x)
      (μ (probe S i) x)
dependentProbeSuiteOfView∘viewOfDependentProbeSuite {O = O} S i x =
  ≈-refl (O i) (μ (probe S i) x)

-- The promised representation equivalence, packaged.
dependentProbeSuiteViewEquiv
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → DependentProbeSuiteViewEquiv X I O
dependentProbeSuiteViewEquiv {X = X} {I = I} {O = O} =
  record
    { toSuite = dependentProbeSuiteOfView {I = I} {O = O}
    ; toView  = viewOfDependentProbeSuite {I = I} {O = O}
    ; μ-toView-toSuite = viewOfDependentProbeSuite∘dependentProbeSuiteOfView {X = X} {I = I} {O = O}
    ; μ-toSuite-toView = dependentProbeSuiteOfView∘viewOfDependentProbeSuite {X = X} {I = I} {O = O}
    }

-- Packaging as a kernel (decode-first):
-- a dependent probe suite is a kernel with boundary `Π i → O i` and code `X`.
dependentProbeSuiteKernel
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → DependentProbeSuite X I O
  → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓX
dependentProbeSuiteKernel S =
  kernelFromView (viewOfDependentProbeSuite S)

-- Each probe is evaluation of the distributed decode at its index.
probe≈evalᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
    (S : DependentProbeSuite X I O)
  → ∀ i x
  → _≈_ (O i)
      (μ (probe S i) x)
      (Kernel.decode (dependentProbeSuiteKernel S) x i)
probe≈evalᵈ {O = O} S i x =
  ≈-refl (O i) (μ (probe S i) x)
