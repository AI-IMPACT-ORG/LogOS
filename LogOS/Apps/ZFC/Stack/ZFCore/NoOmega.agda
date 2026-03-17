{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.NoOmega where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.View using (View; μ)

open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)
import LogOS.Apps.ZFC.Stack.ZFCore.Signature as Signature
open Signature using
  ( ZFSignatureCore
  ; ZFSignaturePowerset
  ; ZFSignatureSeparation
  ; ZFSignatureReplacement
  ; ZFSignatureNoOmega
  )
open import LogOS.Apps.ZFC.Stack.ZFCore.Laws using
  ( ZFLawsCore
  ; ZFLawsPowerset
  ; ZFLawsSeparation
  ; ZFLawsReplacement
  ; ZFLawsFoundation
  ; succ-spec-from-core
  )

record ZFLawsNoOmega {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignatureNoOmega C)
  : Set (lsuc ℓ) where
  open ZFSignatureNoOmega Sig
  field
    coreLaws : ZFLawsCore C coreSig
    powersetLaws : ZFLawsPowerset C powSig
    separationLaws : ZFLawsSeparation C sepSig
    replacementLaws : ZFLawsReplacement C repSig
    foundationLaws : ZFLawsFoundation C coreSig

  open ZFLawsCore coreLaws public
  open ZFLawsPowerset powersetLaws public
  open ZFLawsSeparation separationLaws public
  open ZFLawsReplacement replacementLaws public
  open ZFLawsFoundation foundationLaws public

record ZFStackNoOmega {ℓ : Level} : Set (lsuc ℓ) where
  field
    ctx : SetContext {ℓ}
    sig : ZFSignatureNoOmega ctx
    laws : ZFLawsNoOmega ctx sig

  open SetContext ctx public
  open ZFSignatureNoOmega sig public
  open ZFLawsNoOmega laws public
  module SigD = Signature.DerivedCore (ZFSignatureNoOmega.coreSig sig)

  ZeroV : View (⊤ {ℓ}) SetBnd
  ZeroV = SigD.ZeroV

  singletonV : View SetU SetBnd
  singletonV = SigD.singletonV

  union₂V : View (SetU × SetU) SetBnd
  union₂V = SigD.union₂V

  SuccV : View SetU SetBnd
  SuccV = SigD.SuccV

  zero-spec : ∀ z → ¬ (z ∈ μ ZeroV tt)
  zero-spec = empty-spec

  succ-spec
    : ∀ x z
    → (z ∈ μ SuccV x) ↔ ((z ∈ x) ⊎ (z ≈ x))
  succ-spec x z =
    succ-spec-from-core
      (ZFSignatureNoOmega.coreSig sig)
      (ZFLawsNoOmega.coreLaws laws)
      x
      z
