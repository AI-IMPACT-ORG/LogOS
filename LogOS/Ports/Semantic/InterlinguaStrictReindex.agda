{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.InterlinguaStrictReindex where

-- Interlingua for strict syntax across signature reindexing:
-- the canonical translation is exactly the user-provided `mapFml`.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.Reindex using (reindexKernelWithFml; reindex-satS-withFml)
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.Reindex using (reindexLogicKernelWithFml; reindexLogic-satS-withFml)

open import LogOS.Ports.Semantic.InterlinguaCore as InterlinguaCore
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero
open import LogOS.Adapters.Views.SatMor using
  ( satMor-reindexKernel-strict
  ; satMor-reindexLogicKernel-strict
  )

module ForKernel
  {ℓ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K : Kernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → Kernel.Fml K)
  where

  K₁ : Kernel Sig₁ Q
  K₁ = reindexKernelWithFml σ K mapFml

  SatS₁ : LogOSSignature.Cosp Sig₁ → Fml₁ → Set ℓ
  SatS₁ = Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K₁)

  SatS₂ : LogOSSignature.Cosp Sig₂ → Kernel.Fml K → Set ℓ
  SatS₂ = Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K)

  P₁ : PresentationC (LogOSSignature.Cosp Sig₁) Fml₁ SatS₁
  P₁ = canonicalPresentation SatS₁

  P₂ : PresentationC (LogOSSignature.Cosp Sig₂) (Kernel.Fml K) SatS₂
  P₂ = canonicalPresentation SatS₂

  m : SatMor (LogOSSignature.Cosp Sig₁) Fml₁ SatS₁
              (LogOSSignature.Cosp Sig₂) (Kernel.Fml K) SatS₂
  m = satMor-reindexKernel-strict σ K mapFml
  module I = Hetero.For m P₁ P₂

  translate≈mapFml : I._≈⇒_ I.translate mapFml
  translate≈mapFml = InterlinguaCore.canonical-translate≈mapCon m

  mapFml-preserves-Sat
    : ∀ p φ
    → SatS₁ p φ ↔ SatS₂ (SigHom.mapCosp σ p) (mapFml φ)
  mapFml-preserves-Sat = reindex-satS-withFml σ K mapFml

  mapFml-unique
    : ∀ (t : Fml₁ → Kernel.Fml K)
    → I.SemPreserving t
    → I._≈⇒_ t mapFml
  mapFml-unique t pres p φ =
    Prop.↔-trans
      (I.translate-unique t pres p φ)
      (translate≈mapFml p φ)

module ForLogicKernel
  {ℓ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K : LogicKernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → LogicKernel.Fml K)
  where

  K₁ : LogicKernel Sig₁ Q
  K₁ = reindexLogicKernelWithFml σ K mapFml

  SatS₁ : LogOSSignature.Cosp Sig₁ → Fml₁ → Set ℓ
  SatS₁ = Truth.StrictTruth.StrictLayer.Sat_S (LogicKernel.Strict K₁)

  SatS₂ : LogOSSignature.Cosp Sig₂ → LogicKernel.Fml K → Set ℓ
  SatS₂ = Truth.StrictTruth.StrictLayer.Sat_S (LogicKernel.Strict K)

  P₁ : PresentationC (LogOSSignature.Cosp Sig₁) Fml₁ SatS₁
  P₁ = canonicalPresentation SatS₁

  P₂ : PresentationC (LogOSSignature.Cosp Sig₂) (LogicKernel.Fml K) SatS₂
  P₂ = canonicalPresentation SatS₂

  m : SatMor (LogOSSignature.Cosp Sig₁) Fml₁ SatS₁
              (LogOSSignature.Cosp Sig₂) (LogicKernel.Fml K) SatS₂
  m = satMor-reindexLogicKernel-strict σ K mapFml
  module I = Hetero.For m P₁ P₂

  translate≈mapFml : I._≈⇒_ I.translate mapFml
  translate≈mapFml = InterlinguaCore.canonical-translate≈mapCon m

  mapFml-preserves-Sat
    : ∀ p φ
    → SatS₁ p φ ↔ SatS₂ (SigHom.mapCosp σ p) (mapFml φ)
  mapFml-preserves-Sat = reindexLogic-satS-withFml σ K mapFml

  mapFml-unique
    : ∀ (t : Fml₁ → LogicKernel.Fml K)
    → I.SemPreserving t
    → I._≈⇒_ t mapFml
  mapFml-unique t pres p φ =
    Prop.↔-trans
      (I.translate-unique t pres p φ)
      (translate≈mapFml p φ)
