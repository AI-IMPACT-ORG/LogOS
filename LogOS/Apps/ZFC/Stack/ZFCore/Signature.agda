{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.Signature where

open import LogOS.Prelude
open import LogOS.LT.View using (View; μ; pullbackView; _∘View_)

open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)

-- ------------------------------------------------------------------------
-- Signature profiles
--
-- The ZF stack interface is intentionally split into small “profiles” so that
-- downstream code can state the minimal constructor assumptions it requires.

record ZFSignatureCore {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  open SetContext C
  field
    EmptyV    : View (⊤ {ℓ}) SetBnd
    PairV     : View (SetU × SetU) SetBnd
    UnionV    : View SetU SetBnd

record ZFSignaturePowerset {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  open SetContext C
  field
    PowersetV : View SetU SetBnd

record ZFSignatureOmega {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  open SetContext C
  field
    OmegaV    : View (⊤ {ℓ}) SetBnd

record ZFSignatureSeparation {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  open SetContext C
  field
    SeparationV
      : (P : SetContext.SetU C → Set ℓ)
      → View (SetContext.SetU C) (SetContext.SetBnd C)

record ZFSignatureReplacement {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  open SetContext C
  field
    ReplacementV
      : (R : SetContext.SetU C → SetContext.SetU C → Set ℓ)
      → View (SetContext.SetU C) (SetContext.SetBnd C)

record ZFSignatureConstructors {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  field
    coreSig : ZFSignatureCore C
    powSig  : ZFSignaturePowerset C

  open ZFSignatureCore coreSig public
  open ZFSignaturePowerset powSig public

record ZFSignatureBase {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  field
    constructorSig : ZFSignatureConstructors C
    omegaSig       : ZFSignatureOmega C

  open ZFSignatureConstructors constructorSig public
  open ZFSignatureOmega omegaSig public

record ZFSignatureComprehension {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  field
    sepSig : ZFSignatureSeparation C
    repSig : ZFSignatureReplacement C

  open ZFSignatureSeparation sepSig public
  open ZFSignatureReplacement repSig public

record ZFSignatureNoOmega {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  field
    constructorSig   : ZFSignatureConstructors C
    comprehensionSig : ZFSignatureComprehension C

  open ZFSignatureConstructors constructorSig public
  open ZFSignatureComprehension comprehensionSig public

record ZFSignature {ℓ : Level} (C : SetContext {ℓ}) : Set (lsuc ℓ) where
  field
    baseSig          : ZFSignatureBase C
    comprehensionSig : ZFSignatureComprehension C

  open ZFSignatureBase baseSig public
  open ZFSignatureComprehension comprehensionSig public

zfSignatureConstructors
  : ∀ {ℓ : Level} {C : SetContext {ℓ}}
  → ZFSignatureCore C
  → ZFSignaturePowerset C
  → ZFSignatureConstructors C
zfSignatureConstructors coreSig powSig =
  record
    { coreSig = coreSig
    ; powSig = powSig
    }

zfSignatureBase
  : ∀ {ℓ : Level} {C : SetContext {ℓ}}
  → ZFSignatureConstructors C
  → ZFSignatureOmega C
  → ZFSignatureBase C
zfSignatureBase constructorSig omegaSig =
  record
    { constructorSig = constructorSig
    ; omegaSig = omegaSig
    }

zfSignatureComprehension
  : ∀ {ℓ : Level} {C : SetContext {ℓ}}
  → ZFSignatureSeparation C
  → ZFSignatureReplacement C
  → ZFSignatureComprehension C
zfSignatureComprehension sepSig repSig =
  record
    { sepSig = sepSig
    ; repSig = repSig
    }

zfSignatureNoOmega
  : ∀ {ℓ : Level} {C : SetContext {ℓ}}
  → ZFSignatureCore C
  → ZFSignaturePowerset C
  → ZFSignatureSeparation C
  → ZFSignatureReplacement C
  → ZFSignatureNoOmega C
zfSignatureNoOmega coreSig powSig sepSig repSig =
  record
    { constructorSig = zfSignatureConstructors coreSig powSig
    ; comprehensionSig = zfSignatureComprehension sepSig repSig
    }

zfSignature
  : ∀ {ℓ : Level} {C : SetContext {ℓ}}
  → ZFSignatureCore C
  → ZFSignaturePowerset C
  → ZFSignatureOmega C
  → ZFSignatureSeparation C
  → ZFSignatureReplacement C
  → ZFSignature C
zfSignature coreSig powSig omegaSig sepSig repSig =
  record
    { baseSig =
        zfSignatureBase
          (zfSignatureConstructors coreSig powSig)
          omegaSig
    ; comprehensionSig =
        zfSignatureComprehension sepSig repSig
    }

-- Signature-derived helpers: some standard constructors are definable from the
-- core ZF constructor views (no additional axioms).

module DerivedCore {ℓ : Level} {C : SetContext {ℓ}} (Sig : ZFSignatureCore C) where
  open SetContext C
  open ZFSignatureCore Sig

  -- von Neumann 0 is definitionally the empty set in this presentation.
  ZeroV : View (⊤ {ℓ}) SetBnd
  ZeroV = EmptyV

  singletonV : View SetU SetBnd
  singletonV = pullbackView (λ x → x , x) PairV

  union₂V : View (SetU × SetU) SetBnd
  union₂V = UnionV ∘View PairV

  -- Successor: succ x = x ∪ {x}.
  SuccV : View SetU SetBnd
  SuccV = pullbackView (λ x → x , μ singletonV x) union₂V

module Derived {ℓ : Level} {C : SetContext {ℓ}} (Sig : ZFSignature C) where
  module D = DerivedCore (ZFSignature.coreSig Sig)
  open D public
