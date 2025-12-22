{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.ClosureEndo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Minimal.Con
open import LogOS.Kernel.Endo

open import LogOS.Kernel.TensorDSL

-- The ZFC closure endomap collects all constructors/axioms we want the universe
-- to satisfy. It is expressed as a boundary endomap so the tensor/endomap DSL can
-- produce its least fixed point (Th⋆).

-- ZFC-specific naming: a “closure component” is just a kernel closure-step.
ClosureComponent
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Set (lsuc ℓ)
ClosureComponent = ClosureStep

-- Flow-close a component: apply the component and then take Flow-shadow.
-- This preserves the sandwich bounds, hence is the default “closure step”
-- constructor in the endo-DSL style.

Flow-closeComponent
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ClosureComponent K → ClosureComponent K
Flow-closeComponent {K = K} = Flow-closeStep K

infixr 6 _⊕Closure_

_⊕Closure_
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ClosureComponent K → ClosureComponent K → ClosureComponent K
_⊕Closure_ K = _∘Step_ {K = K}

record ZFCClosure {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                  (K : Kernel Sig Q) : Set (lsuc ℓ) where
  field
    component  : ClosureComponent K
    endo       : Endo K
    hf≤closure : _≤₂_ K (idEndo K) endo
    closure≤Flow : _≤₂_ K endo (Flow-Endo K)

closureFromComponent
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ClosureComponent K → ZFCClosure K
closureFromComponent {K = K} comp = record
  { component  = comp
  ; endo       = ClosureStep.endo comp
  ; hf≤closure = ClosureStep.infl comp
  ; closure≤Flow = ClosureStep.leFlow comp
  }

-- Experimental:
-- This file provides a kernel-native “closure-step” API intended for an
-- alternative (future) ZFC route based on composing closure components and
-- taking a least fixed point via the tensor/endomap DSL.
--
-- It is not required for the production WFGraph ZF/ZFC route.
