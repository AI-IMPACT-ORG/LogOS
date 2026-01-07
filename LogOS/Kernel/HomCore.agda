{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.HomCore where

open import LogOS.Prelude

open import LogOS.Algebra.ConAlg

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

    -- Up-to-decode equality on code maps (helpful for quotiented initiality).
    infix 4 _≈Code_
    _≈Code_ : Code K₁ → Code K₁ → Set ℓ
    _≈Code_ γ δ = decode K₁ γ ≡ decode K₁ δ

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

