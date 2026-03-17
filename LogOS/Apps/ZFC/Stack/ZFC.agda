{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFC where

open import LogOS.Prelude
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom using (KernelHom)
import LogOS.LT.Stack as LTStack
import LogOS.LT.Stack.Extend as LTStackExtend
open import LogOS.LT.Stack using (Stack; stackKernel; programKernel; opKernel)

open import LogOS.Apps.ZFC.Stack.ZFCore as ZF using
    ( SetContext
    ; ZFSignatureCore
    ; ZFLawsCore
    ; ZFStack
    )

import LogOS.Apps.ZFC.SetTheory.ChoiceAxiom as AC

-- ZFC: extend the ZF stack with a choice transformer.

-- Choice only depends on a small fragment of the ZF stack interface: the
-- pairing constructor (to present ordered pairs) and its membership law.
record ZFPairingStack {ℓ : Level} : Set (lsuc ℓ) where
  field
    ctx  : ZF.SetContext {ℓ}
    sig  : ZF.ZFSignatureCore ctx
    laws : ZF.ZFLawsCore ctx sig

  open ZF.SetContext ctx public
  open ZF.ZFSignatureCore sig public
  open ZF.ZFLawsCore laws public
pairingStackFromZFStack : ∀ {ℓ : Level} → ZF.ZFStack {ℓ} → ZFPairingStack {ℓ}
pairingStackFromZFStack S =
  record
    { ctx = ZF.ZFStack.ctx S
    ; sig = ZF.ZFStack.coreSig S
    ; laws = ZF.ZFStack.coreLaws S
    }

record ZFCSignature {ℓ : Level} (S : ZFPairingStack {ℓ}) : Set (lsuc ℓ) where
  open ZFPairingStack S
  ChoiceCode : Set ℓ
  ChoiceCode =
    Σ SetU (λ X → (∀ x → x ∈ X → Σ SetU (λ y → y ∈ x)))

  field
    ChoiceV : View ChoiceCode SetBnd

record ZFCLaws {ℓ : Level} (S : ZFPairingStack {ℓ}) (Sig : ZFCSignature S)
  : Set (lsuc ℓ) where
  open ZFPairingStack S
  open ZFCSignature Sig
  module Choice =
    AC.ChoiceAxiomLocal
      SetU
      _∈_
      _≈_
      (λ x y → μ PairV (x , y) , pairing-spec x y)

  field
    choice-spec
      : ∀ (X : SetU)
        (nonempty : ∀ x → x ∈ X → Σ SetU (λ y → y ∈ x))
      → Choice.ChoiceFunctionOn (μ ChoiceV (X , nonempty)) X

record ZFCStack {ℓ : Level} : Set (lsuc ℓ) where
  field
    zf   : ZF.ZFStack {ℓ}
    zfcSig  : ZFCSignature (pairingStackFromZFStack zf)
    zfcLaws : ZFCLaws (pairingStackFromZFStack zf) zfcSig

  open ZF.ZFStack zf public
  open ZFCSignature zfcSig public
  open ZFCLaws zfcLaws public
  -- ------------------------------------------------------------------------
  -- Stack packaging: ZFC primitives as a single transformer stack.
  --
  -- ZF already exposes a "primitive constructor" stack (`primStack`) as a
  -- derived presentation of the constructor views.
  --
  -- Here we refine that stack by adding a single additional operation
  -- corresponding to the choice transformer.

  primStackZFC : Stack {ℓ} {ℓ} {ℓ} {ℓ}
  primStackZFC =
    LTStackExtend.extendStack
      primStack
      (⊤ {ℓ})
      (λ _ → ChoiceCode)
      (λ _ → ChoiceV)

  PrimKZFC : Kernel ℓ ℓ (ℓ ⊔ ℓ)
  PrimKZFC = stackKernel primStackZFC

  PrimProgramKZFC : Kernel ℓ ℓ (ℓ ⊔ ℓ ⊔ ℓ)
  PrimProgramKZFC = programKernel primStackZFC

  choiceOp : LTStack.Op primStackZFC
  choiceOp = inj₂ tt

  ChoiceK : Kernel ℓ ℓ ℓ
  ChoiceK = opKernel primStackZFC choiceOp

  -- ZF primitives embed into the ZFC primitive kernel by tagging each
  -- constructor code with the canonical left injection.
  PrimK→PrimKZFC : KernelHom PrimK PrimKZFC
  PrimK→PrimKZFC =
    LTStackExtend.stackKernel↪
      primStack
      (⊤ {ℓ})
      (λ _ → ChoiceCode)
      (λ _ → ChoiceV)

  PrimProgramK→PrimProgramKZFC : KernelHom PrimProgramK PrimProgramKZFC
  PrimProgramK→PrimProgramKZFC =
    LTStackExtend.programKernel↪
      primStack
      (⊤ {ℓ})
      (λ _ → ChoiceCode)
      (λ _ → ChoiceV)
