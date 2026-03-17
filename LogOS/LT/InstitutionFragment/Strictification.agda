{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.InstitutionFragment.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.InstitutionFragment using (InstitutionFragmentData)

record InstitutionFragmentStrictLaws
  {ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat : Level}
  (I : InstitutionFragmentData ℓSig ℓHom ℓSenCon ℓSenRel ℓMod ℓSat)
  : Set (lsuc (ℓSig ⊔ ℓHom ⊔ ℓSenCon ⊔ ℓSenRel ⊔ ℓMod ⊔ ℓSat)) where
  open InstitutionFragmentData I renaming
    ( Sig    to Sig₀
    ; Hom    to Hom₀
    ; Sen    to Sen₀
    ; Mod    to Mod₀
    ; idHom  to idHom₀
    ; _∘Hom_ to _∘Hom₀_
    ; mapSen to mapSen₀
    ; mapMod to mapMod₀
    )
  field
    mapSen-id
      : ∀ {S : Sig₀} (s : Con (Sen₀ S))
      → mapSen₀ idHom₀ s ≡ s

    mapSen-comp
      : ∀ {S S' S'' : Sig₀} (g : Hom₀ S' S'') (f : Hom₀ S S') (s : Con (Sen₀ S))
      → mapSen₀ (g ∘Hom₀ f) s ≡ mapSen₀ g (mapSen₀ f s)

    mapMod-id
      : ∀ {S : Sig₀} (m : Mod₀ S)
      → mapMod₀ idHom₀ m ≡ m

    mapMod-comp
      : ∀ {S S' S'' : Sig₀} (g : Hom₀ S' S'') (f : Hom₀ S S') (m : Mod₀ S)
      → mapMod₀ (g ∘Hom₀ f) m ≡ mapMod₀ g (mapMod₀ f m)

open InstitutionFragmentStrictLaws public
