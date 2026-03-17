{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.ProbeSuiteRepresentation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Representation theorem (probe suites / stacks of views).
--
-- A “stack of probes” into a local interface `O`, indexed by `I`,
--
--   probe : I → View X O
--
-- is μ-equivalent (pointwise on observation) to a single view into the distributed boundary
--
--   View X (FunPreorder I O)   ≃μ   ProbeSuite X I O.
--
-- Readings:
-- - many transformers into one local boundary  ↔  one transformer into a product boundary;
-- - “semantic function X → (I → O)” is the same as an indexed family of semantic probes.
--
-- This gives a formal core of the guiding statement:
--   logic = observation boundary + (stack of) transformers.
--
-- v1.1 note (locality discipline):
-- the canonical theorem is the *dependent* one
-- (`LogOS.LT.Theorems.DependentProbeSuiteRepresentation`). This module is the
-- constant-family special case wrapper (take `Oᵈ = λ _ → O`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _≈_; ≈-refl)
open import LogOS.LT.FunPreorder using (FunPreorder)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; kernelFromView)
open import LogOS.LT.Presentation.ObservationInitiality using
  ( ProbeSuite
  ; probe
  ; toDependentProbeSuite
  ; fromDependentProbeSuite
  )

import LogOS.LT.Theorems.DependentProbeSuiteRepresentation as Dep

-- μ-level equivalence packaging (no record/function extensionality assumptions).
--
-- This is the intended meaning of “equivalent” in this module: the two
-- presentations compute observationally equivalent boundary values, pointwise.
record ProbeSuiteViewEquiv
  {ℓX ℓI ℓOCon ℓORel : Level}
  (X : Set ℓX) (I : Set ℓI) (O : ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    toSuite : View X (FunPreorder I O) → ProbeSuite X I O
    toView  : ProbeSuite X I O → View X (FunPreorder I O)

    μ-toView-toSuite
      : ∀ (V : View X (FunPreorder I O)) (x : X) (i : I)
      → _≈_ O (μ (toView (toSuite V)) x i) (μ V x i)

    μ-toSuite-toView
      : ∀ (S : ProbeSuite X I O) (i : I) (x : X)
      → _≈_ O (μ (probe (toSuite (toView S)) i) x) (μ (probe S i) x)

-- View → ProbeSuite (split a distributed observation into its local probes).
probeSuiteOfView
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → View X (FunPreorder I O)
  → ProbeSuite X I O
probeSuiteOfView {O = O} V =
  fromDependentProbeSuite (Dep.dependentProbeSuiteOfView {O = λ _ → O} V)

-- ProbeSuite → View (bundle all probes into one distributed observation).
--
-- This is `viewOfDependentProbeSuite` from the dependent theorem, specialised
-- to constant families.
viewOfProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → ProbeSuite X I O
  → View X (FunPreorder I O)
viewOfProbeSuite {O = O} S =
  Dep.viewOfDependentProbeSuite {O = λ _ → O} (toDependentProbeSuite S)

-- Round-trip laws (pointwise on observations).
--
-- We state these as pointwise mutual refinements of `μ`, rather than equality of `View`
-- records (to avoid committing to a particular extensionality principle for records).

viewOfProbeSuite∘probeSuiteOfView
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    (V : View X (FunPreorder I O))
  → ∀ x i
  → _≈_ O
      (μ (viewOfProbeSuite (probeSuiteOfView {O = O} V)) x i)
      (μ V x i)
viewOfProbeSuite∘probeSuiteOfView {O = O} V =
  Dep.viewOfDependentProbeSuite∘dependentProbeSuiteOfView {O = λ _ → O} V

probeSuiteOfView∘viewOfProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    (S : ProbeSuite X I O)
  → ∀ i x
  → _≈_ O
      (μ (probe (probeSuiteOfView {O = O} (viewOfProbeSuite S)) i) x)
      (μ (probe S i) x)
probeSuiteOfView∘viewOfProbeSuite {O = O} S =
  Dep.dependentProbeSuiteOfView∘viewOfDependentProbeSuite {O = λ _ → O} (toDependentProbeSuite S)

-- The promised representation equivalence, packaged.
probeSuiteViewEquiv
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → ProbeSuiteViewEquiv X I O
probeSuiteViewEquiv {X = X} {I = I} {O = O} =
  record
    { toSuite = probeSuiteOfView {I = I} {O = O}
    ; toView  = viewOfProbeSuite {I = I} {O = O}
    ; μ-toView-toSuite = viewOfProbeSuite∘probeSuiteOfView {X = X} {I = I} {O = O}
    ; μ-toSuite-toView = probeSuiteOfView∘viewOfProbeSuite {X = X} {I = I} {O = O}
    }

-- Packaging as a kernel (decode-first):
-- a probe suite is a kernel with boundary `I → O` and code `X`.
probeSuiteKernel
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → ProbeSuite X I O
  → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓX
probeSuiteKernel S = kernelFromView (viewOfProbeSuite S)

-- Each probe is evaluation of the distributed decode at its index.
probe≈eval
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    (S : ProbeSuite X I O)
  → ∀ i x
  → _≈_ O
      (μ (probe S i) x)
      (Kernel.decode (probeSuiteKernel S) x i)
probe≈eval {O = O} S i x =
  ≈-refl O (μ (probe S i) x)
