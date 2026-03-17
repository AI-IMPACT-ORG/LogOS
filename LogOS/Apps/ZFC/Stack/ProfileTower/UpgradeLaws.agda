{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ProfileTower.UpgradeLaws where

open import LogOS.Prelude
open import LogOS.Apps.ZFC.Stack.ProfileTower.Core using
  ( ChoiceUpgrade
  ; ZFStackBase
  ; ZFUpgrades
  ; zfStackFromBase
  )
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.ZFC as ZFC

zfStack-coreLaws
  : ∀ {ℓ : Level}
    (B : ZFStackBase {ℓ})
    (upg : ZFUpgrades B)
  → ZF.ZFLawsCore (ZFStackBase.ctx B) (ZFStackBase.coreSig B)
zfStack-coreLaws B upg = ZF.ZFStack.coreLaws (zfStackFromBase B upg)

zfStack-foundationLaws
  : ∀ {ℓ : Level}
    (B : ZFStackBase {ℓ})
    (upg : ZFUpgrades B)
  → ZF.ZFLawsFoundation (ZFStackBase.ctx B) (ZFStackBase.coreSig B)
zfStack-foundationLaws B upg =
  ZF.ZFStack.foundationLaws (zfStackFromBase B upg)

zfcStack-choiceLaws
  : ∀ {ℓ : Level}
    (zf : ZF.ZFStack {ℓ})
    (upg : ChoiceUpgrade (ZFC.pairingStackFromZFStack zf))
  → ZFC.ZFCLaws
      (ZFC.pairingStackFromZFStack zf)
      (ChoiceUpgrade.sig upg)
zfcStack-choiceLaws _ upg = ChoiceUpgrade.laws upg
