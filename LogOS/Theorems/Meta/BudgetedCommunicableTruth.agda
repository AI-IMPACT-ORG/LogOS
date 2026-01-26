{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.BudgetedCommunicableTruth where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary; _≈CP_)

import LogOS.Kernel as K
import LogOS.Kernel.Graded as KG
import LogOS.Kernel.LogicKernel as LK

import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObsLK

-- Box/BoxAt-based “communicability” (observer semantics) specialisations.
--
-- This complements `LogOS.Theorems.Meta.CommunicableTruth`, which uses the
-- computational step `FlowCode`. Here we treat the stabilization modalities
-- `Box` / `BoxAt` themselves as the step in `ObserverCore`.

module ForKernel
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K₀ : K.Kernel Sig Q)
  where

  Code : Set ℓ
  Code = K.Kernel.Code K₀

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (K.Kernel.BB K₀)

  decode : Code → ConPreorder.Con CP
  decode = K.Kernel.decode K₀

  PrBox
    : ∀ {ℓT ℓC : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
  PrBox {ℓC = ℓC} TruthK =
    ObsCore.Pred⋆≈ {ℓP = ℓC} CP decode (K.Box K₀) TruthK

  TruthK→PrBox
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (K.Box K₀ γ))
    → ∀ {γ} → TruthK γ → PrBox {ℓC = ℓT} TruthK γ
  TruthK→PrBox TruthK ext stable tγ =
    ObsCore.Pred⋆≈-contains CP decode (K.Box K₀) TruthK TruthK A-self tγ
    where
      A-self : ObsCore.Admissible≈ Code CP decode (K.Box K₀) TruthK TruthK
      A-self = record
        { ext≈   = ext
        ; sound  = λ {γ} t → t
        ; stable = stable
        }

  -- ------------------------------------------------------------------------
  -- Stability bridge: FlowCode vs Box ∘ Body
  --
  -- `FlowCode` is the computational step (Guard ∘ Body), while `Box` is the
  -- code-level stabilization modality induced by the guarded closure.
  --
  -- On decoded meaning, `FlowCode γ` and `Box (Body γ)` coincide, so any
  -- decode-extensional predicate can transport between the two.

  decode-FlowCode≡decode-BoxBody
    : ∀ γ
    → K.Kernel.decode K₀ (K.FlowCode K₀ γ)
      ≡
      K.Kernel.decode K₀ (K.Box K₀ (K.Kernel.Body K₀ γ))
  decode-FlowCode≡decode-BoxBody = K.decode-FlowCode≡decode-BoxBody K₀

  FlowCode↔BoxBody
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → ∀ γ → TruthK (K.FlowCode K₀ γ) ↔ TruthK (K.Box K₀ (K.Kernel.Body K₀ γ))
  FlowCode↔BoxBody TruthK ext γ =
    ObsCore.DecodeExtensional≈-cong {CP = CP} {decode = decode} {P = TruthK} ext (eq γ)
    where
      eq : ∀ γ′ →
        _≈CP_ CP (decode (K.FlowCode K₀ γ′))
                 (decode (K.Box K₀ (K.Kernel.Body K₀ γ′)))
      eq γ′
        rewrite decode-FlowCode≡decode-BoxBody γ′
        = (ConPreorder.refl CP , ConPreorder.refl CP)

  FlowStable→BoxBodyStable
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (K.FlowCode K₀ γ))
    → (∀ γ → TruthK γ ↔ TruthK (K.Box K₀ (K.Kernel.Body K₀ γ)))
  FlowStable→BoxBodyStable TruthK ext stableFlow =
    ST.stableUnder TruthK ext stableFlow
    where
      eqStep : ∀ γ →
        _≈CP_ CP (decode (K.FlowCode K₀ γ))
                 (decode (K.Box K₀ (K.Kernel.Body K₀ γ)))
      eqStep γ
        rewrite decode-FlowCode≡decode-BoxBody γ
        = (ConPreorder.refl CP , ConPreorder.refl CP)

      module ST =
        ObsCore.StepTransport≈
          CP
          decode
          (K.FlowCode K₀)
          (λ γ → K.Box K₀ (K.Kernel.Body K₀ γ))
          eqStep

  BoxBodyStable→FlowStable
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (K.Box K₀ (K.Kernel.Body K₀ γ)))
    → (∀ γ → TruthK γ ↔ TruthK (K.FlowCode K₀ γ))
  BoxBodyStable→FlowStable TruthK ext stableBox =
    ST.stableUnder TruthK ext stableBox
    where
      eqStep : ∀ γ →
        _≈CP_ CP (decode (K.Box K₀ (K.Kernel.Body K₀ γ)))
                 (decode (K.FlowCode K₀ γ))
      eqStep γ
        rewrite sym (decode-FlowCode≡decode-BoxBody γ)
        = (ConPreorder.refl CP , ConPreorder.refl CP)

      module ST =
        ObsCore.StepTransport≈
          CP
          decode
          (λ γ → K.Box K₀ (K.Kernel.Body K₀ γ))
          (K.FlowCode K₀)
          eqStep

module ForGradedKernel
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K₀ : KG.GradedKernel Sig Q)
  where

  Code : Set ℓ
  Code = KG.GradedKernel.Code K₀

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (KG.GradedKernel.BB K₀)

  decode = KG.GradedKernel.decode K₀

  PrAt
    : ∀ {ℓT ℓC : Level}
      (TruthK : Code → Set ℓT)
      (g : QAdapter.Scale Q)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
  PrAt {ℓC = ℓC} TruthK g =
    ObsCore.Pred⋆≈ {ℓP = ℓC} CP decode (KG.BoxAt K₀ g) TruthK

  TruthK→PrAt
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
      (g : QAdapter.Scale Q)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (KG.BoxAt K₀ g γ))
    → ∀ {γ} → TruthK γ → PrAt {ℓC = ℓT} TruthK g γ
  TruthK→PrAt TruthK g ext stable tγ =
    ObsCore.Pred⋆≈-contains CP decode (KG.BoxAt K₀ g) TruthK TruthK A-self tγ
    where
      A-self : ObsCore.Admissible≈ Code CP decode (KG.BoxAt K₀ g) TruthK TruthK
      A-self = record
        { ext≈   = ext
        ; sound  = λ {γ} t → t
        ; stable = stable
        }

  -- ------------------------------------------------------------------------
  -- Stability bridge: FlowCode vs BoxAt(step-grade) ∘ Body

  stepGrade : QAdapter.Scale Q
  stepGrade = KG.GradedKernel.step-grade K₀

  decode-FlowCode≡decode-BoxAt-step-body
    : ∀ γ
    → KG.GradedKernel.decode K₀ (KG.FlowCode K₀ γ)
      ≡
      KG.GradedKernel.decode K₀
        (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ))
  decode-FlowCode≡decode-BoxAt-step-body = KG.decode-FlowCode≡decode-BoxAt-step-body K₀

  FlowCode↔BoxAt-step-body
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → ∀ γ →
        TruthK (KG.FlowCode K₀ γ)
        ↔ TruthK (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ))
  FlowCode↔BoxAt-step-body TruthK ext γ =
    ObsCore.DecodeExtensional≈-cong {CP = CP} {decode = decode} {P = TruthK} ext (eq γ)
    where
      eq : ∀ γ′ →
        _≈CP_ CP (decode (KG.FlowCode K₀ γ′))
                 (decode (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ′)))
      eq γ′
        rewrite decode-FlowCode≡decode-BoxAt-step-body γ′
        = (ConPreorder.refl CP , ConPreorder.refl CP)

  FlowStable→BoxAt-step-bodyStable
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (KG.FlowCode K₀ γ))
    → (∀ γ → TruthK γ ↔ TruthK (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ)))
  FlowStable→BoxAt-step-bodyStable TruthK ext stableFlow =
    ST.stableUnder TruthK ext stableFlow
    where
      eqStep : ∀ γ →
        _≈CP_ CP (decode (KG.FlowCode K₀ γ))
                 (decode (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ)))
      eqStep γ
        rewrite decode-FlowCode≡decode-BoxAt-step-body γ
        = (ConPreorder.refl CP , ConPreorder.refl CP)

      module ST =
        ObsCore.StepTransport≈
          CP
          decode
          (KG.FlowCode K₀)
          (λ γ → KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ))
          eqStep

  BoxAt-step-bodyStable→FlowStable
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ)))
    → (∀ γ → TruthK γ ↔ TruthK (KG.FlowCode K₀ γ))
  BoxAt-step-bodyStable→FlowStable TruthK ext stableBox =
    ST.stableUnder TruthK ext stableBox
    where
      eqStep : ∀ γ →
        _≈CP_ CP (decode (KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ)))
                 (decode (KG.FlowCode K₀ γ))
      eqStep γ
        rewrite sym (decode-FlowCode≡decode-BoxAt-step-body γ)
        = (ConPreorder.refl CP , ConPreorder.refl CP)

      module ST =
        ObsCore.StepTransport≈
          CP
          decode
          (λ γ → KG.BoxAt K₀ stepGrade (KG.GradedKernel.Body K₀ γ))
          (KG.FlowCode K₀)
          eqStep

module ForLogicKernel
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K₀ : LK.LogicKernel Sig Q)
  where

  module O = ObsLK.For K₀

  Code : Set ℓ
  Code = LK.LogicKernel.Code K₀

  decode = LK.LogicKernel.decode K₀

  PrAt
    : ∀ {ℓT ℓC : Level}
      (TruthK : Code → Set ℓT)
      (g : LK.GTier.Step (LK.LogicKernel.G K₀))
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
  PrAt {ℓC = ℓC} TruthK g =
    ObsCore.Pred⋆≈ {ℓP = ℓC} O.CP decode (LK.BoxAt K₀ g) TruthK

  TruthK→PrAt
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
      (g : LK.GTier.Step (LK.LogicKernel.G K₀))
    → ObsCore.DecodeExtensional≈ O.CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (LK.BoxAt K₀ g γ))
    → ∀ {γ} → TruthK γ → PrAt {ℓC = ℓT} TruthK g γ
  TruthK→PrAt TruthK g ext stable tγ =
    ObsCore.Pred⋆≈-contains O.CP decode (LK.BoxAt K₀ g) TruthK TruthK A-self tγ
    where
      A-self : ObsCore.Admissible≈ Code O.CP decode (LK.BoxAt K₀ g) TruthK TruthK
      A-self = record
        { ext≈   = ext
        ; sound  = λ {γ} t → t
        ; stable = stable
        }

  -- ------------------------------------------------------------------------
  -- Stability bridge: FlowCode vs BoxAt(step) ∘ Body

  decode-FlowCode≡decode-BoxAt-step-body
    : ∀ γ
    → LK.LogicKernel.decode K₀ (LK.FlowCode K₀ γ)
      ≡
      LK.LogicKernel.decode K₀
        (LK.BoxAt K₀ (LK.GTier.step (LK.LogicKernel.G K₀)) (LK.LogicKernel.Body K₀ γ))
  decode-FlowCode≡decode-BoxAt-step-body = O.decode-stepFlowCode≡decode-step

  FlowCode↔BoxAt-step-body
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ O.CP decode TruthK
    → ∀ γ →
        TruthK (LK.FlowCode K₀ γ)
        ↔ TruthK (LK.BoxAt K₀ (LK.GTier.step (LK.LogicKernel.G K₀)) (LK.LogicKernel.Body K₀ γ))
  FlowCode↔BoxAt-step-body TruthK ext γ =
    ObsCore.DecodeExtensional≈-cong {CP = O.CP} {decode = decode} {P = TruthK} ext
      (O.decode-stepFlowCode≈decode-step γ)

  FlowStable→BoxAt-step-bodyStable
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ O.CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (LK.FlowCode K₀ γ))
    → (∀ γ → TruthK γ ↔ TruthK (LK.BoxAt K₀ (LK.GTier.step (LK.LogicKernel.G K₀)) (LK.LogicKernel.Body K₀ γ)))
  FlowStable→BoxAt-step-bodyStable TruthK ext stableFlow =
    let
      module ST =
        ObsCore.StepTransport≈
          O.CP
          decode
          (LK.FlowCode K₀)
          (λ γ → LK.BoxAt K₀ (LK.GTier.step (LK.LogicKernel.G K₀)) (LK.LogicKernel.Body K₀ γ))
          O.decode-stepFlowCode≈decode-step
    in
    ST.stableUnder TruthK ext stableFlow

  BoxAt-step-bodyStable→FlowStable
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional≈ O.CP decode TruthK
    → (∀ γ → TruthK γ ↔ TruthK (LK.BoxAt K₀ (LK.GTier.step (LK.LogicKernel.G K₀)) (LK.LogicKernel.Body K₀ γ)))
    → (∀ γ → TruthK γ ↔ TruthK (LK.FlowCode K₀ γ))
  BoxAt-step-bodyStable→FlowStable TruthK ext stableBox =
    let
      module ST =
        ObsCore.StepTransport≈
          O.CP
          decode
          (λ γ → LK.BoxAt K₀ (LK.GTier.step (LK.LogicKernel.G K₀)) (LK.LogicKernel.Body K₀ γ))
          (LK.FlowCode K₀)
          O.decode-step≈decode-stepFlowCode
    in
    ST.stableUnder TruthK ext stableBox
