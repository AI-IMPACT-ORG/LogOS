{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Locality.Lifts where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.FunPreorder using (pointwise≡→≈)
open import LogOS.LT.Sup.FinSup using (FinSup)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO)
import LogOS.LT.FunPreorder.Pointwise as Pointwise
open import LogOS.Ports.Locality.Core using (LocalBoundary)

pointwiseClosure
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → GuardedClosure (O i))
  → GuardedClosure (LocalBoundary I O)
pointwiseClosure = Pointwise.pointwiseClosure

pointwiseFinSup
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → FinSup (O i))
  → FinSup (LocalBoundary I O)
pointwiseFinSup = Pointwise.pointwiseFinSup

pointwiseSigmaDCPO
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → SigmaDCPO (O i))
  → SigmaDCPO (LocalBoundary I O)
pointwiseSigmaDCPO = Pointwise.pointwiseSigmaDCPO

pointwise≡→≈LocalBoundary
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {F G : Con (LocalBoundary I O)}
  → (∀ i → F i ≡ G i)
  → _≈_ (LocalBoundary I O) F G
pointwise≡→≈LocalBoundary {I = I} {O = O} =
  pointwise≡→≈ {A = I} {O = O}
