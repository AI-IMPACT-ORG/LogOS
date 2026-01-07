{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.HomWithGradeCore where

open import LogOS.Prelude

open import LogOS.Minimal.Adapter
open import LogOS.Algebra.ConAlg

-- Shared “structural hom + grade map” core.
--
-- This is the graded analogue of `LogOS.Kernel.HomCore`, but supports morphisms
-- between objects that live over different `QAdapter`s.

record Ops {ℓ : Level} : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    Obj      : QAdapter ℓ → Set (lsuc (lsuc ℓ))
    conAlgOf : ∀ {Q : QAdapter ℓ} → Obj Q → ConAlg {ℓ}

    Code   : ∀ {Q : QAdapter ℓ} → Obj Q → Set ℓ
    encode : ∀ {Q : QAdapter ℓ} (K : Obj Q) → ConAlg.Con_bnd (conAlgOf K) → Code K
    decode : ∀ {Q : QAdapter ℓ} (K : Obj Q) → Code K → ConAlg.Con_bnd (conAlgOf K)

    reify        : ∀ {Q : QAdapter ℓ} (K : Obj Q) → Code K → Code K
    reify-decode : ∀ {Q : QAdapter ℓ} (K : Obj Q) (γ : Code K) → decode K (reify K γ) ≡ decode K γ

    Body        : ∀ {Q : QAdapter ℓ} (K : Obj Q) → Code K → Code K
    Body∂       : ∀ {Q : QAdapter ℓ} (K : Obj Q) → ConAlg.Con_bnd (conAlgOf K) → ConAlg.Con_bnd (conAlgOf K)
    body-decode : ∀ {Q : QAdapter ℓ} (K : Obj Q) (γ : Code K)
               → decode K (Body K γ) ≡ Body∂ K (decode K γ)

    GradeHom        : (Q₁ Q₂ : QAdapter ℓ) → Set (lsuc ℓ)
    idGradeHom      : ∀ {Q : QAdapter ℓ} → GradeHom Q Q
    composeGradeHom : ∀ {Q₁ Q₂ Q₃ : QAdapter ℓ} → GradeHom Q₁ Q₂ → GradeHom Q₂ Q₃ → GradeHom Q₁ Q₃

module WithOps {ℓ : Level} (ops : Ops {ℓ}) where
  open Ops ops

  record HomWithGrade {Q₁ Q₂ : QAdapter ℓ} (K₁ : Obj Q₁) (K₂ : Obj Q₂) : Set (lsuc (lsuc ℓ)) where
    field
      con-hom    : ConAlgHom≡ (conAlgOf K₁) (conAlgOf K₂)
      mapCode    : Code K₁ → Code K₂
      map-encode : ∀ c → mapCode (encode K₁ c) ≡ encode K₂ (ConAlgHom≡.map∂ con-hom c)
      map-decode : ∀ γ → decode K₂ (mapCode γ) ≡ ConAlgHom≡.map∂ con-hom (decode K₁ γ)
      grade-hom  : GradeHom Q₁ Q₂

    infix 4 _≈Code_
    _≈Code_ : Code K₁ → Code K₁ → Set ℓ
    _≈Code_ γ δ = decode K₁ γ ≡ decode K₁ δ

  idHomWithGrade
    : ∀ {Q : QAdapter ℓ}
      (K : Obj Q)
    → HomWithGrade K K
  idHomWithGrade K =
    record
      { con-hom    = idHom≡ (conAlgOf K)
      ; mapCode    = λ γ → γ
      ; map-encode = λ _ → refl
      ; map-decode = λ _ → refl
      ; grade-hom  = idGradeHom
      }

  composeHomWithGrade
    : ∀ {Q₁ Q₂ Q₃ : QAdapter ℓ}
      {K₁ : Obj Q₁} {K₂ : Obj Q₂} {K₃ : Obj Q₃}
    → HomWithGrade K₁ K₂ → HomWithGrade K₂ K₃ → HomWithGrade K₁ K₃
  composeHomWithGrade h₁ h₂ =
    record
      { con-hom    = composeHom≡ (HomWithGrade.con-hom h₁) (HomWithGrade.con-hom h₂)
      ; mapCode    = λ γ → HomWithGrade.mapCode h₂ (HomWithGrade.mapCode h₁ γ)
      ; map-encode = λ c →
          trans
            (cong (HomWithGrade.mapCode h₂) (HomWithGrade.map-encode h₁ c))
            (HomWithGrade.map-encode h₂
              (ConAlgHom≡.map∂ (HomWithGrade.con-hom h₁) c))
      ; map-decode = λ γ →
          trans
            (HomWithGrade.map-decode h₂ (HomWithGrade.mapCode h₁ γ))
            (cong (ConAlgHom≡.map∂ (HomWithGrade.con-hom h₂))
                  (HomWithGrade.map-decode h₁ γ))
      ; grade-hom  = composeGradeHom (HomWithGrade.grade-hom h₁) (HomWithGrade.grade-hom h₂)
      }

  map-reify-decode
    : ∀ {Q₁ Q₂ : QAdapter ℓ}
      {K₁ : Obj Q₁} {K₂ : Obj Q₂}
      (h : HomWithGrade K₁ K₂)
      (γ : Code K₁)
    → decode K₂ (HomWithGrade.mapCode h (reify K₁ γ))
      ≡ ConAlgHom≡.map∂ (HomWithGrade.con-hom h) (decode K₁ γ)
  map-reify-decode {K₁ = K₁} {K₂ = K₂} h γ =
    let open HomWithGrade h in
    trans (map-decode (reify K₁ γ))
          (cong (ConAlgHom≡.map∂ con-hom) (reify-decode K₁ γ))

  map-body-decode
    : ∀ {Q₁ Q₂ : QAdapter ℓ}
      {K₁ : Obj Q₁} {K₂ : Obj Q₂}
      (h : HomWithGrade K₁ K₂)
      (γ : Code K₁)
    → decode K₂ (HomWithGrade.mapCode h (Body K₁ γ))
      ≡ ConAlgHom≡.map∂ (HomWithGrade.con-hom h) (Body∂ K₁ (decode K₁ γ))
  map-body-decode {K₁ = K₁} {K₂ = K₂} h γ =
    let open HomWithGrade h in
    trans (map-decode (Body K₁ γ))
          (cong (ConAlgHom≡.map∂ con-hom) (body-decode K₁ γ))

