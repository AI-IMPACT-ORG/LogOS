{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.ObservationInitiality where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Initiality of pullback refinement for views and probe suites.
--
-- Pullback refinement is the coarsest refinement
-- respecting an explicit observation interface, and this scales from a
-- single probe to a whole probe suite (cone of views).
--
-- Engineering reading:
-- - a view is a probe/sensor/readout into an interface preorder
-- - a refinement relation is admissible iff it is monotone w.r.t. the chosen probes
-- - the induced pullback refinements are the coarsest (least discriminating) ones satisfying that
--
-- This module makes the “many equivalent definitions” story explicit:
-- any alternative presentation that respects the same observations automatically
-- transports into the canonical refinement.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; refl⊑)
open import LogOS.LT.FunPreorder using (FunPreorder; DFunPreorder)
open import LogOS.LT.View using (View; μ; _⊑[_]_; pullbackView)
open import LogOS.LT.Presentation using
  ( Presentation
  ; CompletePresentation
  ; canonicalPresentation
  ; canonicalComplete
  )
open import LogOS.LT.Derivability using
  ( DerivationSystem
  ; canonicalDerivationSystem
  )
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; _⇒_; _⇒∂_; obs; transportObs)

-- --------------------------------------------------------------------------
-- Dependent probe suites (observation interface may vary by index).
--
-- This is the canonical v1.1 notion: “locality is relative”, so both the
-- observation preorder and the admissible doctrine may depend on the index.

record DependentProbeSuite
  {ℓX ℓI ℓOCon ℓORel : Level}
  (X : Set ℓX) (I : Set ℓI) (O : I → ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    probe : (i : I) → View X (O i)

open DependentProbeSuite public
suiteViewᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → DependentProbeSuite X I O
  → View X (DFunPreorder I O)
suiteViewᵈ {I = I} {O = O} S =
  record { μ = λ x i → μ (probe S i) x }

infix 4 _⊑⟦_⟧ᵈ_
_⊑⟦_⟧ᵈ_
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → X → DependentProbeSuite X I O → X → Set (ℓI ⊔ ℓORel)
x ⊑⟦ S ⟧ᵈ y = x ⊑[ suiteViewᵈ S ] y

-- Minimality: any relation respecting every probe is contained in the suite refinement.
SuiteForcedᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
    (S : DependentProbeSuite X I O)
  → (≼ : X → X → Set ℓR)
  → (∀ {x y} → ≼ x y → ∀ i → x ⊑[ probe S i ] y)
  → ∀ {x y} → ≼ x y → x ⊑⟦ S ⟧ᵈ y
SuiteForcedᵈ S ≼ hyp le i = hyp le i

pullbackSuiteᵈ
  : ∀ {ℓX ℓY ℓI ℓOCon ℓORel}
    {X : Set ℓX} {Y : Set ℓY} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → (f : Y → X)
  → DependentProbeSuite X I O
  → DependentProbeSuite Y I O
pullbackSuiteᵈ f S =
  record { probe = λ i → pullbackView f (probe S i) }

private
  mkSuitePresentation
    : ∀ {ℓX ℓR ℓOCon ℓORel}
      {X : Set ℓX}
      {O : ConPreorder ℓOCon ℓORel}
    → (V : View X O)
    → (_≼_ : X → X → Set ℓR)
    → (refl≼ : ∀ {x} → _≼_ x x)
    → (trans≼ : ∀ {a b c} → _≼_ a b → _≼_ b c → _≼_ a c)
    → (∀ {x y} → _≼_ x y → x ⊑[ V ] y)
    → Presentation {ℓR = ℓR} V
  mkSuitePresentation V _≼_ refl≼ trans≼ sound =
    record
      { _≼_ = _≼_
      ; refl≼ = refl≼
      ; trans≼ = trans≼
      ; observe-mono = sound
      }

  mkSuiteDerivationSystem
    : ∀ {ℓX ℓR ℓOCon ℓORel}
      {X : Set ℓX}
      {O : ConPreorder ℓOCon ℓORel}
    → (V : View X O)
    → (_≼_ : X → X → Set ℓR)
    → (refl≼ : ∀ {x} → _≼_ x x)
    → (trans≼ : ∀ {a b c} → _≼_ a b → _≼_ b c → _≼_ a c)
    → (∀ {x y} → _≼_ x y → x ⊑[ V ] y)
    → (base : X)
    → DerivationSystem {ℓR = ℓR} V
  mkSuiteDerivationSystem V _≼_ refl≼ trans≼ sound base =
    record
      { presentation = mkSuitePresentation V _≼_ refl≼ trans≼ sound
      ; base = base
      }

suitePresentationᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
    (S : DependentProbeSuite X I O)
  → (_≼_ : X → X → Set ℓR)
  → (refl≼ : ∀ {x} → _≼_ x x)
  → (trans≼ : ∀ {a b c} → _≼_ a b → _≼_ b c → _≼_ a c)
  → (∀ {x y} → _≼_ x y → ∀ i → x ⊑[ probe S i ] y)
  → Presentation {ℓR = ℓR} (suiteViewᵈ S)
suitePresentationᵈ S _≼_ refl≼ trans≼ sound =
  mkSuitePresentation
    (suiteViewᵈ S)
    _≼_
    refl≼
    trans≼
    (SuiteForcedᵈ S _≼_ sound)

suiteDerivationSystemᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
    (S : DependentProbeSuite X I O)
  → (_≼_ : X → X → Set ℓR)
  → (refl≼ : ∀ {x} → _≼_ x x)
  → (trans≼ : ∀ {a b c} → _≼_ a b → _≼_ b c → _≼_ a c)
  → (∀ {x y} → _≼_ x y → ∀ i → x ⊑[ probe S i ] y)
  → (base : X)
  → DerivationSystem {ℓR = ℓR} (suiteViewᵈ S)
suiteDerivationSystemᵈ S _≼_ refl≼ trans≼ sound base =
  mkSuiteDerivationSystem
    (suiteViewᵈ S)
    _≼_
    refl≼
    trans≼
    (SuiteForcedᵈ S _≼_ sound)
    base

canonicalSuitePresentationᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → (S : DependentProbeSuite X I O)
  → Presentation {ℓR = (ℓI ⊔ ℓORel)} (suiteViewᵈ S)
canonicalSuitePresentationᵈ S = canonicalPresentation (suiteViewᵈ S)

canonicalSuiteCompleteᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → (S : DependentProbeSuite X I O)
  → CompletePresentation (canonicalSuitePresentationᵈ S)
canonicalSuiteCompleteᵈ S = canonicalComplete (suiteViewᵈ S)

canonicalSuiteDerivationSystemᵈ
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : I → ConPreorder ℓOCon ℓORel}
  → (S : DependentProbeSuite X I O)
  → (base : X)
  → DerivationSystem {ℓR = (ℓI ⊔ ℓORel)} (suiteViewᵈ S)
canonicalSuiteDerivationSystemᵈ S base =
  canonicalDerivationSystem (suiteViewᵈ S) base

-- --------------------------------------------------------------------------
-- Uniform probe suites (constant-family special case).

record ProbeSuite
  {ℓX ℓI ℓOCon ℓORel : Level}
  (X : Set ℓX) (I : Set ℓI) (O : ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    probe : I → View X O

open ProbeSuite public
-- Uniform/dependent bridge: treat a uniform suite as a dependent suite over a
-- constant family.
toDependentProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → ProbeSuite X I O
  → DependentProbeSuite X I (λ _ → O)
toDependentProbeSuite S = record { probe = probe S }

fromDependentProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → DependentProbeSuite X I (λ _ → O)
  → ProbeSuite X I O
fromDependentProbeSuite S = record { probe = DependentProbeSuite.probe S }

suiteView
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → ProbeSuite X I O
  → View X (FunPreorder I O)
suiteView {O = O} S = suiteViewᵈ {O = λ _ → O} (toDependentProbeSuite S)

infix 4 _⊑⟦_⟧_
_⊑⟦_⟧_
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → X → ProbeSuite X I O → X → Set (ℓI ⊔ ℓORel)
x ⊑⟦ S ⟧ y = x ⊑[ suiteView S ] y

-- Minimality: any relation respecting every probe is contained in the suite refinement.
SuiteForced
  : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    (S : ProbeSuite X I O)
  → (≼ : X → X → Set ℓR)
  → (∀ {x y} → ≼ x y → ∀ i → x ⊑[ probe S i ] y)
  → ∀ {x y} → ≼ x y → x ⊑⟦ S ⟧ y
SuiteForced {O = O} S ≼ hyp =
  SuiteForcedᵈ {O = λ _ → O} (toDependentProbeSuite S) ≼ hyp

pullbackSuite
  : ∀ {ℓX ℓY ℓI ℓOCon ℓORel}
    {X : Set ℓX} {Y : Set ℓY} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → (f : Y → X)
  → ProbeSuite X I O
  → ProbeSuite Y I O
pullbackSuite {O = O} f S =
  fromDependentProbeSuite
    (pullbackSuiteᵈ {O = λ _ → O} f (toDependentProbeSuite S))

suitePresentation
  : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    (S : ProbeSuite X I O)
  → (_≼_ : X → X → Set ℓR)
  → (refl≼ : ∀ {x} → _≼_ x x)
  → (trans≼ : ∀ {a b c} → _≼_ a b → _≼_ b c → _≼_ a c)
  → (∀ {x y} → _≼_ x y → ∀ i → x ⊑[ probe S i ] y)
  → Presentation {ℓR = ℓR} (suiteView S)
suitePresentation S _≼_ refl≼ trans≼ sound =
  suitePresentationᵈ
    (toDependentProbeSuite S)
    _≼_
    refl≼
    trans≼
    sound

suiteDerivationSystem
  : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    (S : ProbeSuite X I O)
  → (_≼_ : X → X → Set ℓR)
  → (refl≼ : ∀ {x} → _≼_ x x)
  → (trans≼ : ∀ {a b c} → _≼_ a b → _≼_ b c → _≼_ a c)
  → (∀ {x y} → _≼_ x y → ∀ i → x ⊑[ probe S i ] y)
  → (base : X)
  → DerivationSystem {ℓR = ℓR} (suiteView S)
suiteDerivationSystem S _≼_ refl≼ trans≼ sound base =
  suiteDerivationSystemᵈ
    (toDependentProbeSuite S)
    _≼_
    refl≼
    trans≼
    sound
    base

canonicalSuitePresentation
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → (S : ProbeSuite X I O)
  → Presentation {ℓR = (ℓI ⊔ ℓORel)} (suiteView S)
canonicalSuitePresentation S =
  canonicalSuitePresentationᵈ (toDependentProbeSuite S)

canonicalSuiteComplete
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → (S : ProbeSuite X I O)
  → CompletePresentation (canonicalSuitePresentation S)
canonicalSuiteComplete S =
  canonicalSuiteCompleteᵈ (toDependentProbeSuite S)

canonicalSuiteDerivationSystem
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → (S : ProbeSuite X I O)
  → (base : X)
  → DerivationSystem {ℓR = (ℓI ⊔ ℓORel)} (suiteView S)
canonicalSuiteDerivationSystem S base =
  canonicalSuiteDerivationSystemᵈ (toDependentProbeSuite S) base

-- --------------------------------------------------------------------------
-- Kernels: decode-induced code refinement is a pullback refinement.

CodeRefineForced
  : ∀ {ℓ ℓRel ℓCode ℓR}
    (K : Kernel ℓ ℓRel ℓCode)
  → (≼ : Code K → Code K → Set ℓR)
  → (∀ {γ δ} → ≼ γ δ → _⊑_ (bnd K) (decode K γ) (decode K δ))
  → ∀ {γ δ} → ≼ γ δ → _⊑_ (CodePreorder K) γ δ
CodeRefineForced K ≼ hyp le = hyp le

MorRefineForced∂
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (≼ : KernelHom K K' → KernelHom K K' → Set ℓR)
  → (∀ {f g} → ≼ f g → (∀ γ → _⊑_ (bnd K') (transportObs {K = K} f γ) (transportObs {K = K} g γ)))
  → ∀ {f g} → ≼ f g → f ⇒∂ g
MorRefineForced∂ _ hyp le = hyp le

MorRefineForced
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (≼ : KernelHom K K' → KernelHom K K' → Set ℓR)
  → (∀ {f g} → ≼ f g → (∀ γ → _⊑_ (bnd K') (obs f γ) (obs g γ)))
  → ∀ {f g} → ≼ f g → f ⇒ g
MorRefineForced _ hyp le = hyp le
