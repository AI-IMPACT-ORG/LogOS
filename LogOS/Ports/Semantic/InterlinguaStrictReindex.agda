{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
open import LogOS.Kernel.Reindex using (reindexKernelWithFml; reindexLogic-satS-withFml)

open import LogOS.Ports.Semantic.HeteroInterlinguaCore as InterlinguaCore
open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem; PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Adapters.Views.SatMor using (satMor-reindexKernel-strict)

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

  S₁ : SatSystem
  S₁ = satSystem (LogOSSignature.Cosp Sig₁) Fml₁ SatS₁

  S₂ : SatSystem
  S₂ = satSystem (LogOSSignature.Cosp Sig₂) (Kernel.Fml K) SatS₂

  P₁ : PresentationC S₁
  P₁ = InterlinguaCore.canonicalPresentation S₁

  P₂ : PresentationC S₂
  P₂ = InterlinguaCore.canonicalPresentation S₂

  m : SatMor S₁ S₂
  m = satMor-reindexKernel-strict σ K mapFml
  module I = InterlinguaCore.For m P₁ P₂

  translate≈mapFml : I._≈⇒_ I.translate mapFml
  translate≈mapFml = InterlinguaCore.canonical-translate≈mapCon m

  mapFml-preserves-Sat
    : ∀ p φ
    → SatS₁ p φ ↔ SatS₂ (SigHom.mapCosp σ p) (mapFml φ)
  mapFml-preserves-Sat = reindexLogic-satS-withFml σ K mapFml

  mapFml-unique
    : ∀ (t : Fml₁ → Kernel.Fml K)
    → I.SemPreserving t
    → I._≈⇒_ t mapFml
  mapFml-unique t pres =
    let
      t≈tr : I._≈⇒_ t I.translate
      t≈tr = I.translate-unique t pres

      tr≈map : I._≈⇒_ I.translate mapFml
      tr≈map = translate≈mapFml
    in
    ( (λ p φ sat → I.Trans≈⇒ tr≈map p φ (I.Trans≈⇒ t≈tr p φ sat))
    , (λ p φ sat → I.Trans≈⇐ t≈tr p φ (I.Trans≈⇐ tr≈map p φ sat))
    )
