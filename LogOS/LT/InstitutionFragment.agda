{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.InstitutionFragment where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; MonoMap; _≈_; ≈-refl)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_; map∂; mapCode; map∂-mono)
open import LogOS.LT.Contracts using (_⊨_[_]; models-map)

record InstitutionFragmentData
  (ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat : Level)
  : Set (lsuc (ℓSig ⊔ ℓHom ⊔ ℓSenCon ⊔ ℓSenRel ⊔ ℓMod ⊔ ℓSat)) where
  infixr 9 _∘Hom_
  field
    Sig : Set ℓSig
    Hom : Sig → Sig → Set ℓHom

    idHom  : ∀ {S} → Hom S S
    _∘Hom_ : ∀ {S S' S''} → Hom S' S'' → Hom S S' → Hom S S''

    Sen : Sig → ConPreorder ℓSenCon ℓSenRel
    Mod : Sig → Set ℓMod

    mapSen : ∀ {S S'} → Hom S S' → Con (Sen S) → Con (Sen S')
    mapSen-mono : ∀ {S S'} (h : Hom S S') → MonoMap (Sen S) (Sen S') (mapSen h)

    mapMod : ∀ {S S'} → Hom S S' → Mod S → Mod S'

    Sat : ∀ {S} → Mod S → Con (Sen S) → Set ℓSat

    sat-condition
      : ∀ {S S'} (h : Hom S S') {m : Mod S} {s : Con (Sen S)}
      → Sat m s
      → Sat (mapMod h m) (mapSen h s)

open InstitutionFragmentData public

record InstitutionFragmentLaws
  {ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat : Level}
  (I : InstitutionFragmentData ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat)
  : Set (lsuc (ℓSig ⊔ ℓHom ⊔ ℓSenCon ⊔ ℓSenRel ⊔ ℓMod ⊔ ℓSat)) where
  open InstitutionFragmentData I renaming
    ( Sig    to Sig₀
    ; Hom    to Hom₀
    ; Sen    to Sen₀
    ; idHom  to idHom₀
    ; _∘Hom_ to _∘Hom₀_
    ; mapSen to mapSen₀
    )
  field
    mapSen-id≈
      : ∀ {S : Sig₀} (s : Con (Sen₀ S))
      → _≈_ (Sen₀ S) (mapSen₀ idHom₀ s) s

    mapSen-comp≈
      : ∀ {S S' S'' : Sig₀} (g : Hom₀ S' S'') (f : Hom₀ S S') (s : Con (Sen₀ S))
      → _≈_ (Sen₀ S'')
          (mapSen₀ (g ∘Hom₀ f) s)
          (mapSen₀ g (mapSen₀ f s))

open InstitutionFragmentLaws public

record InstitutionFragment
  (ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat : Level)
  : Set (lsuc (ℓSig ⊔ ℓHom ⊔ ℓSenCon ⊔ ℓSenRel ⊔ ℓMod ⊔ ℓSat)) where
  field
    structure : InstitutionFragmentData ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat
    laws : InstitutionFragmentLaws structure

open InstitutionFragment public

record KernelInstitutionCodeLaws
  {ℓ ℓRel ℓCode : Level}
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where
  field
    mapMod-id≈
      : ∀ {K : Kernel ℓ ℓRel ℓCode} (γ : Code K)
      → _≈_ (CodePreorder K) (mapCode (idKernelHom K) γ) γ

    mapMod-comp≈
      : ∀ {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
        (g : KernelHom K₂ K₃)
        (f : KernelHom K₁ K₂)
        (γ : Code K₁)
      → _≈_ (CodePreorder K₃)
          (mapCode (g ∘ f) γ)
          (mapCode g (mapCode f γ))

open KernelInstitutionCodeLaws public

KernelInstitutionFragmentData
  : ∀ {ℓ ℓRel ℓCode : Level}
  → InstitutionFragmentData
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
      ℓ
      ℓRel
      ℓCode
      ℓRel
KernelInstitutionFragmentData {ℓ} {ℓRel} {ℓCode} =
  record
    { Sig = Kernel ℓ ℓRel ℓCode
    ; Hom = KernelHom
    ; idHom = λ {K} → idKernelHom K
    ; _∘Hom_ = _∘_
    ; Sen = bnd
    ; Mod = Code
    ; mapSen = map∂
    ; mapSen-mono = map∂-mono
    ; mapMod = mapCode
    ; Sat = λ {K} γ c → K ⊨ γ [ c ]
    ; sat-condition = λ {S} {S'} h sat → models-map h sat
    }

KernelInstitutionFragmentLaws
  : ∀ {ℓ ℓRel ℓCode : Level}
  → InstitutionFragmentLaws (KernelInstitutionFragmentData {ℓ} {ℓRel} {ℓCode})
KernelInstitutionFragmentLaws =
  record
    { mapSen-id≈ = λ {S} s →
        ≈-refl (bnd S) (map∂ (idKernelHom S) s)
    ; mapSen-comp≈ = λ {S'' = S''} g f s →
        ≈-refl (bnd S'') (map∂ (g ∘ f) s)
    }

KernelInstitutionFragmentCodeLaws
  : ∀ {ℓ ℓRel ℓCode : Level}
  → KernelInstitutionCodeLaws {ℓ} {ℓRel} {ℓCode}
KernelInstitutionFragmentCodeLaws =
  record
    { mapMod-id≈ = λ {K} γ →
        ≈-refl (CodePreorder K) (mapCode (idKernelHom K) γ)
    ; mapMod-comp≈ = λ {K₃ = K₃} g f γ →
        ≈-refl (CodePreorder K₃) (mapCode (g ∘ f) γ)
    }

KernelInstitutionFragment
  : ∀ {ℓ ℓRel ℓCode : Level}
  → InstitutionFragment
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
      ℓ
      ℓRel
      ℓCode
      ℓRel
KernelInstitutionFragment =
  record
    { structure = KernelInstitutionFragmentData
    ; laws = KernelInstitutionFragmentLaws
    }
