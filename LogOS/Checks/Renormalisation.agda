{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Renormalisation where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List)
open import LogOS.Prelude.List.Ops using (_∈_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Flow using (Stable; elem)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.AbstractQuanticNucleus using (QuanticNucleus)
import LogOS.Ports.Valuation.AbstractQuanticNucleus as Nucleus
import LogOS.Ports.Valuation.AbstractConnesKreimer as CK

module RenormalisationWitness
  {ℓCon ℓRel ℓP : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (JP : JoinPrequantale CP)
  (P : Set ℓP)
  (N : QuanticNucleus JP)
  where

  module QN = Nucleus.QuanticNucleusLocal N
  module CKN = CK.CK JP P

  stableProductLeast
    : ∀ (x y z : Stable {CP = CP} (LogOS.LT.Flow.GuardedClosure.Flow (QuanticNucleus.GC N)))
    → _⊑_ CP ((JoinPrequantale._·_ JP) (elem x) (elem y)) (elem z)
    → _⊑_ CP (elem (QN.stable-· x y)) (elem z)
  stableProductLeast x y z xy≤z =
    QN.stable-·-least x y z xy≤z

  stableJoinListLeast
    : ∀ (x z : Stable {CP = CP} (LogOS.LT.Flow.GuardedClosure.Flow (QuanticNucleus.GC N)))
      (xs : List (Stable {CP = CP} (LogOS.LT.Flow.GuardedClosure.Flow (QuanticNucleus.GC N))))
    → _⊑_ CP (elem x) (elem z)
    → (∀ {w} → w ∈ xs → _⊑_ CP (elem w) (elem z))
    → _⊑_ CP (elem (QN.stableJoinList x xs)) (elem z)
  stableJoinListLeast x z xs x≤z xs≤z =
    QN.stableJoinList-least x xs z x≤z xs≤z

  _ : ∀ (φ : CK.Tree P → Con CP) → CKN.StableChar N
  _ = CKN.renormalisedCharStable N

  renormalisedConvolutionLeast
    : ∀ (φ ψ : CK.Tree P → Con CP)
      (χ : CKN.StableChar N)
      (t : CK.Tree P)
    → _⊑_ CP ((φ CKN.⋆ ψ) t) (elem (χ t))
    → _⊑_ CP (CKN.renormalisedConvolution N φ ψ t) (elem (χ t))
  renormalisedConvolutionLeast φ ψ χ t convolution≤χ =
    CKN.renormalisedConvolution-least N φ ψ χ t convolution≤χ
