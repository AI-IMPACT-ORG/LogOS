{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ProfileTower.Core where

-- A compact “profile tower” view on the ZF/ZFC stack interface.
--
-- Goal:
-- make the strong constructor profiles (Separation/Replacement/Choice) explicit
-- *upgrade steps* rather than treating them as structurally inseparable from
-- the base transformer stack.
--
-- This module keeps explicit track of what is (and is not) derived:
-- - the upgrades below are *packaging* boundaries for assumptions, not proofs
--   that the corresponding axioms follow from weaker ones.
-- - the primary benefit is dependency auditability and the ability to swap in
--   alternative upgrade sources (e.g. `InfinityUpgrade` for ω).

open import LogOS.Prelude
open import LogOS.LT.Stack as LTStack using
  ( Stack
  ; Op
  ; stackKernel
  ; programKernel
  ; opKernel
  )
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom using (KernelHom)
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.ZFC as ZFC
import LogOS.Apps.ZFC.Stack.ZFCore.PrimitiveStack as PrimitiveStack

-- ------------------------------------------------------------------------
-- ZF tower: separate the “comprehension-like” profiles from the base stack.

record ZFStackBase {ℓ : Level} : Set (lsuc ℓ) where
  field
    ctx : ZF.SetContext {ℓ}

    coreSig  : ZF.ZFSignatureCore ctx
    powSig   : ZF.ZFSignaturePowerset ctx
    omegaSig : ZF.ZFSignatureOmega ctx

    coreLaws      : ZF.ZFLawsCore ctx coreSig
    powersetLaws  : ZF.ZFLawsPowerset ctx powSig
    infinityLaws  : ZF.ZFLawsInfinity ctx coreSig omegaSig

  open ZF.SetContext ctx public
  open ZF.ZFSignatureCore coreSig public
  open ZF.ZFSignaturePowerset powSig public
  open ZF.ZFSignatureOmega omegaSig public
  open ZF.ZFLawsCore coreLaws public
  open ZF.ZFLawsPowerset powersetLaws public
  open ZF.ZFLawsInfinity infinityLaws public

record ConstructorLayer {ℓ : Level} (C : ZF.SetContext {ℓ}) (Sig : ZF.ZFSignature C)
  : Set (lsuc ℓ) where
  field
    stack : Stack {ℓ} {ℓ} {ℓ} {ℓ}

  operationKernel : LTStack.Op stack → Kernel ℓ ℓ ℓ
  operationKernel = LTStack.opKernel stack

  layerKernel : Kernel ℓ ℓ ℓ
  layerKernel = LTStack.stackKernel stack

  layerProgram : Kernel ℓ ℓ (ℓ ⊔ ℓ ⊔ ℓ)
  layerProgram = LTStack.programKernel stack

  injectOperation
    : (o : LTStack.Op stack)
    → KernelHom (operationKernel o) layerKernel
  injectOperation = LTStack.injOp stack

constructorLayer
  : ∀ {ℓ : Level} (C : ZF.SetContext {ℓ})
  → (Sig : ZF.ZFSignature C)
  → ConstructorLayer {ℓ} C Sig
constructorLayer C Sig =
  let
    module Prim =
      PrimitiveStack.Primitive
        C
        (ZF.ZFSignature.coreSig Sig)
        (ZF.ZFSignature.powSig Sig)
        (ZF.ZFSignature.omegaSig Sig)

    stack = Prim.primStack
  in
  record
    { stack = stack }

-- Foundation is intentionally separated as an explicit upgrade step:
-- a ZF(C)-Foundation stack is a meaningful intermediate object in the LogOS
-- “assumption ledger” story.
record FoundationUpgrade {ℓ : Level} (B : ZFStackBase {ℓ}) : Set (lsuc ℓ) where
  open ZFStackBase B
  field
    foundationLaws : ZF.ZFLawsFoundation ctx coreSig

  open ZF.ZFLawsFoundation foundationLaws public

record SeparationUpgrade {ℓ : Level} (B : ZFStackBase {ℓ}) : Set (lsuc ℓ) where
  open ZFStackBase B
  field
    sepSig  : ZF.ZFSignatureSeparation ctx
    sepLaws : ZF.ZFLawsSeparation ctx sepSig

  open ZF.ZFSignatureSeparation sepSig public
  open ZF.ZFLawsSeparation sepLaws public

record ReplacementUpgrade {ℓ : Level} (B : ZFStackBase {ℓ}) : Set (lsuc ℓ) where
  open ZFStackBase B
  field
    repSig  : ZF.ZFSignatureReplacement ctx
    repLaws : ZF.ZFLawsReplacement ctx repSig

  open ZF.ZFSignatureReplacement repSig public
  open ZF.ZFLawsReplacement repLaws public

record ZFUpgrades {ℓ : Level} (B : ZFStackBase {ℓ}) : Set (lsuc ℓ) where
  field
    separation : SeparationUpgrade B
    replacement : ReplacementUpgrade B
    foundation : FoundationUpgrade B

open ZFUpgrades public using (separation; replacement; foundation)

zfStackFromBase
  : ∀ {ℓ : Level}
  → (B : ZFStackBase {ℓ})
  → ZFUpgrades B
  → ZF.ZFStack {ℓ}
zfStackFromBase {ℓ} B upg =
  record
    { ctx = ZFStackBase.ctx B
    ; sig = sig
    ; laws = laws
    }
  where
    open ZFStackBase B
    open SeparationUpgrade (separation upg)
    open ReplacementUpgrade (replacement upg)
    open FoundationUpgrade (foundation upg)
    sig : ZF.ZFSignature ctx
    sig =
      ZF.zfSignature coreSig powSig omegaSig sepSig repSig

    laws : ZF.ZFLaws ctx sig
    laws =
      record
        { coreLaws = coreLaws
        ; powersetLaws = powersetLaws
        ; infinityLaws = infinityLaws
        ; separationLaws = sepLaws
        ; replacementLaws = repLaws
        ; foundationLaws = foundationLaws
        }

baseFromZFStack : ∀ {ℓ : Level} → ZF.ZFStack {ℓ} → ZFStackBase {ℓ}
baseFromZFStack S =
  record
    { ctx = ZF.ZFStack.ctx S
    ; coreSig = ZF.ZFStack.coreSig S
    ; powSig = ZF.ZFStack.powSig S
    ; omegaSig = ZF.ZFStack.omegaSig S
    ; coreLaws = ZF.ZFStack.coreLaws S
    ; powersetLaws = ZF.ZFStack.powersetLaws S
    ; infinityLaws = ZF.ZFStack.infinityLaws S
    }

zfUpgradesFromZFStack
  : ∀ {ℓ : Level}
  → (S : ZF.ZFStack {ℓ})
  → ZFUpgrades (baseFromZFStack S)
zfUpgradesFromZFStack S =
  record
    { separation =
        record
          { sepSig = ZF.ZFStack.sepSig S
          ; sepLaws = ZF.ZFStack.separationLaws S
          }
    ; replacement =
        record
          { repSig = ZF.ZFStack.repSig S
          ; repLaws = ZF.ZFStack.replacementLaws S
          }
    ; foundation =
        record
          { foundationLaws = ZF.ZFStack.foundationLaws S }
    }

-- ------------------------------------------------------------------------
-- ZFC tower: choice is an explicit upgrade over the pairing-core fragment.

record ChoiceUpgrade {ℓ : Level} (S : ZFC.ZFPairingStack {ℓ}) : Set (lsuc ℓ) where
  field
    sig  : ZFC.ZFCSignature S
    laws : ZFC.ZFCLaws S sig

  open ZFC.ZFCSignature sig public
  open ZFC.ZFCLaws laws public

zfcStackFromChoice
  : ∀ {ℓ : Level}
  → (zf : ZF.ZFStack {ℓ})
  → ChoiceUpgrade (ZFC.pairingStackFromZFStack zf)
  → ZFC.ZFCStack {ℓ}
zfcStackFromChoice zf upg =
  record
    { zf = zf
    ; zfcSig = ChoiceUpgrade.sig upg
    ; zfcLaws = ChoiceUpgrade.laws upg
    }

choiceUpgradeFromZFCStack
  : ∀ {ℓ : Level}
  → (S : ZFC.ZFCStack {ℓ})
  → ChoiceUpgrade (ZFC.pairingStackFromZFStack (ZFC.ZFCStack.zf S))
choiceUpgradeFromZFCStack S =
  record
    { sig = ZFC.ZFCStack.zfcSig S
    ; laws = ZFC.ZFCStack.zfcLaws S
    }
