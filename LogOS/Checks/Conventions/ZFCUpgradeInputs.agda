{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.ZFCUpgradeInputs where

open import LogOS.Prelude
open import LogOS.Apps.ZFC.Stack.ProfileTower.Core using (ZFStackBase; FoundationUpgrade; ChoiceUpgrade)
open import LogOS.Apps.ZFC.Stack.InfinityUpgrade using (CoKleeneInfinityAssumptions)
open import LogOS.Apps.ZFC.Stack.ZFC using (ZFPairingStack)
open import LogOS.Apps.ZFC.Stack.ZFCore using (ZFStackNoOmega)

foundation-upgrade-is-explicit
  : ∀ {ℓ : Level} {B : ZFStackBase {ℓ}}
  → FoundationUpgrade B
  → FoundationUpgrade B
foundation-upgrade-is-explicit F = F

choice-upgrade-is-explicit
  : ∀ {ℓ : Level} {S : ZFPairingStack {ℓ}}
  → ChoiceUpgrade S
  → ChoiceUpgrade S
choice-upgrade-is-explicit C = C

infinity-upgrade-is-explicit
  : ∀ {ℓ : Level} {S : ZFStackNoOmega {ℓ}}
  → CoKleeneInfinityAssumptions S
  → CoKleeneInfinityAssumptions S
infinity-upgrade-is-explicit I = I
