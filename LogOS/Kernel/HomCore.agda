{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.HomCore where

open import LogOS.Prelude

open import LogOS.Minimal.ConAlg

-- Shared “structural hom” core for kernel-like objects:
-- strict constraint-algebra map + code map + encode/decode coherence.
--
-- This factors out the common part of `LogOS.Kernel.Hom` and
-- `LogOS.Kernel.Graded.Hom` without committing to either G-tier.

record Ops {ℓ : Level} : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    Obj    : Set (lsuc (lsuc ℓ))
    conAlgOf : Obj → ConAlg {ℓ}

    Code   : Obj → Set ℓ
    encode : (K : Obj) → ConAlg.Con_bnd (conAlgOf K) → Code K
    decode : (K : Obj) → Code K → ConAlg.Con_bnd (conAlgOf K)

    -- Additional shape operations used for shared derived lemmas.
    reify        : (K : Obj) → Code K → Code K
    reify-decode : (K : Obj) (γ : Code K) → decode K (reify K γ) ≡ decode K γ

    Body       : (K : Obj) → Code K → Code K
    Body∂      : (K : Obj) → ConAlg.Con_bnd (conAlgOf K) → ConAlg.Con_bnd (conAlgOf K)
    body-decode : (K : Obj) (γ : Code K) → decode K (Body K γ) ≡ Body∂ K (decode K γ)

module WithOps {ℓ : Level} (ops : Ops {ℓ}) where
  open Ops ops

  -- Structural morphism: preserves the constraint algebra (strictly) and code coherence.
  record Hom (K₁ K₂ : Obj) : Set (lsuc (lsuc ℓ)) where
    field
      con-hom   : ConAlgHom≡ (conAlgOf K₁) (conAlgOf K₂)
      mapCode   : Code K₁ → Code K₂
      map-encode : ∀ c → mapCode (encode K₁ c) ≡ encode K₂ (ConAlgHom≡.map∂ con-hom c)
      map-decode : ∀ γ → decode K₂ (mapCode γ) ≡ ConAlgHom≡.map∂ con-hom (decode K₁ γ)

    -- Strict decode equality (`≡`) on code maps (helpful for quotiented initiality).
    infix 4 _≃Code_
    _≃Code_ : Code K₁ → Code K₁ → Set ℓ
    _≃Code_ γ δ = decode K₁ γ ≡ decode K₁ δ

  -- Identity and composition.

  idHom : (K : Obj) → Hom K K
  idHom K = record
    { con-hom    = idHom≡ (conAlgOf K)
    ; mapCode    = λ γ → γ
    ; map-encode = λ _ → refl
    ; map-decode = λ _ → refl
    }

  composeHom
    : ∀ {K₁ K₂ K₃ : Obj}
    → Hom K₁ K₂ → Hom K₂ K₃ → Hom K₁ K₃
  composeHom h₁ h₂ = record
    { con-hom    = composeHom≡ (Hom.con-hom h₁) (Hom.con-hom h₂)
    ; mapCode    = λ γ → Hom.mapCode h₂ (Hom.mapCode h₁ γ)
    ; map-encode = λ c →
        trans
          (cong (Hom.mapCode h₂) (Hom.map-encode h₁ c))
          (Hom.map-encode h₂ (ConAlgHom≡.map∂ (Hom.con-hom h₁) c))
    ; map-decode = λ γ →
        trans
          (Hom.map-decode h₂ (Hom.mapCode h₁ γ))
          (cong (ConAlgHom≡.map∂ (Hom.con-hom h₂)) (Hom.map-decode h₁ γ))
    }

  map∂-id
    : ∀ {K} (c : ConAlg.Con_bnd (conAlgOf K))
    → ConAlgHom≡.map∂ (Hom.con-hom (idHom K)) c ≡ c
  map∂-id _ = refl

  map∂-compose
    : ∀ {K₁ K₂ K₃}
      (h₁ : Hom K₁ K₂)
      (h₂ : Hom K₂ K₃)
      (c : ConAlg.Con_bnd (conAlgOf K₁))
    → ConAlgHom≡.map∂ (Hom.con-hom (composeHom h₁ h₂)) c
      ≡ ConAlgHom≡.map∂ (Hom.con-hom h₂)
          (ConAlgHom≡.map∂ (Hom.con-hom h₁) c)
  map∂-compose _ _ _ = refl

  mapCode-id
    : ∀ {K} (γ : Code K)
    → Hom.mapCode (idHom K) γ ≡ γ
  mapCode-id _ = refl

  mapCode-compose
    : ∀ {K₁ K₂ K₃}
      (h₁ : Hom K₁ K₂)
      (h₂ : Hom K₂ K₃)
      (γ : Code K₁)
    → Hom.mapCode (composeHom h₁ h₂) γ
      ≡ Hom.mapCode h₂ (Hom.mapCode h₁ γ)
  mapCode-compose _ _ _ = refl

  -- Shared derived coherence (decode-level) for `reify` and `Body`.

  map-reify-decode
    : ∀ {K₁ K₂ : Obj}
      (h : Hom K₁ K₂)
      (γ : Code K₁)
    → decode K₂ (Hom.mapCode h (reify K₁ γ))
      ≡ ConAlgHom≡.map∂ (Hom.con-hom h) (decode K₁ γ)
  map-reify-decode {K₁ = K₁} {K₂ = K₂} h γ =
    let open Hom h in
    trans (map-decode (reify K₁ γ))
          (cong (ConAlgHom≡.map∂ con-hom) (reify-decode K₁ γ))

  map-body-decode
    : ∀ {K₁ K₂ : Obj}
      (h : Hom K₁ K₂)
      (γ : Code K₁)
    → decode K₂ (Hom.mapCode h (Body K₁ γ))
      ≡ ConAlgHom≡.map∂ (Hom.con-hom h) (Body∂ K₁ (decode K₁ γ))
  map-body-decode {K₁ = K₁} {K₂ = K₂} h γ =
    let open Hom h in
    trans (map-decode (Body K₁ γ))
          (cong (ConAlgHom≡.map∂ con-hom) (body-decode K₁ γ))
