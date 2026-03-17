{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ProfileTower.Definitional where

open import LogOS.Prelude
open import LogOS.Apps.ZFC.Stack.ProfileTower.Core using
  ( ChoiceUpgrade
  ; ZFStackBase
  ; ZFUpgrades
  ; baseFromZFStack
  ; choiceUpgradeFromZFCStack
  ; zfStackFromBase
  ; zfcStackFromChoice
  )
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.ZFC as ZFC

baseFrom-zfStackFromBase≡
  : ∀ {ℓ : Level}
    (B : ZFStackBase {ℓ})
    (upg : ZFUpgrades B)
  → baseFromZFStack (zfStackFromBase B upg) ≡ B
baseFrom-zfStackFromBase≡ _ _ = refl

choiceUpgradeFrom-zfcStackFromChoice≡
  : ∀ {ℓ : Level}
    (zf : ZF.ZFStack {ℓ})
    (upg : ChoiceUpgrade (ZFC.pairingStackFromZFStack zf))
  → choiceUpgradeFromZFCStack (zfcStackFromChoice zf upg) ≡ upg
choiceUpgradeFrom-zfcStackFromChoice≡ _ _ = refl
