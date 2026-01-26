{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.BudgetedCommunicableTruth where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

import LogOS.Kernel as K
import LogOS.Kernel.Graded as KG
import LogOS.Kernel.LogicKernel as LK

import LogOS.Theorems.Meta.BudgetedCommunicableTruth as BComm
import LogOS.Theorems.Meta.ObserverCore as ObsCore

module Ungraded {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (U : K.Kernel Sig Q) where
  module B = BComm.ForKernel U

  Truth⊤ : B.Code → Set
  Truth⊤ _ = ⊤

  ext : ObsCore.DecodeExtensional≈ B.CP B.decode Truth⊤
  ext _ _ _ p = p

  stable : ∀ γ → Truth⊤ γ ↔ Truth⊤ (K.Box U γ)
  stable _ = record { to = (λ p → p) ; from = (λ p → p) }

  smoke : B.PrBox {ℓC = lzero} Truth⊤ (K.Kernel.γ* U)
  smoke = B.TruthK→PrBox Truth⊤ ext stable tt

module Graded {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (G : KG.GradedKernel Sig Q) where
  module B = BComm.ForGradedKernel G

  Truth⊤ : B.Code → Set
  Truth⊤ _ = ⊤

  ext : ObsCore.DecodeExtensional≈ B.CP B.decode Truth⊤
  ext _ _ _ p = p

  stable : ∀ γ → Truth⊤ γ ↔ Truth⊤ (KG.BoxAt G (QAdapter.e Q) γ)
  stable _ = record { to = (λ p → p) ; from = (λ p → p) }

  smoke : B.PrAt {ℓC = lzero} Truth⊤ (QAdapter.e Q) (KG.GradedKernel.γ* G)
  smoke = B.TruthK→PrAt Truth⊤ (QAdapter.e Q) ext stable tt

module Logic {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (L : LK.LogicKernel Sig Q) where
  module B = BComm.ForLogicKernel L

  Truth⊤ : B.Code → Set
  Truth⊤ _ = ⊤

  ext : ObsCore.DecodeExtensional≈ B.O.CP B.decode Truth⊤
  ext _ _ _ p = p

  g : LK.GTier.Step (LK.LogicKernel.G L)
  g = LK.GTier.step (LK.LogicKernel.G L)

  stable : ∀ γ → Truth⊤ γ ↔ Truth⊤ (LK.BoxAt L g γ)
  stable _ = record { to = (λ p → p) ; from = (λ p → p) }

  smoke : B.PrAt {ℓC = lzero} Truth⊤ g (LK.LogicKernel.γ* L)
  smoke = B.TruthK→PrAt Truth⊤ g ext stable tt
