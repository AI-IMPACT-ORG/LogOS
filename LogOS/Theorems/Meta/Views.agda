{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Views where

-- “Words match reality” meta-theory:
-- package the bridge points that the documentation claims, but as actual lemmas.
--
-- Design constraints:
-- - no new axioms/postulates,
-- - no extensionality (do not collapse preorders),
-- - prove statements up to refinement/equivalence (`_⇒_`, `_≈_`) where appropriate.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom; composeSigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Syntax.Prop as Prop
open import LogOS.Minimal.ConAlg using (idHom≡)

open import LogOS.Kernel using (Kernel)
import LogOS.Kernel.Reindex as Reindex
import LogOS.Kernel.Hom2Cat as K2
import LogOS.Kernel.Hom as KH

import LogOS.Kernel as LK
open import LogOS.Minimal.Truth as Truth

-- ============================================================================
-- 1) Reindexing associativity: coherence as an equivalence in the refinement 2-cat
-- ============================================================================

module ReindexingAssoc
  {ℓ : Level} {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (τ : SigHom Sig₂ Sig₃)
  (K : Kernel Sig₃ Q)
  where

  open Reindex

  private
    A : Kernel Sig₁ Q
    A = reindexKernel σ (reindexKernel τ K)

    B : Kernel Sig₁ Q
    B = reindexKernel (composeSigHom σ τ) K

    CP : Kernel Sig₁ Q → ConPreorder ℓ
    CP X = BulkBoundary.bnd (Kernel.BB X)

  assoc₁ : K2.KernelHom₁ A B
  assoc₁ =
    record
      { hom =
          record
            { con-hom    = idHom≡ (KH.conAlgOf B)
            ; mapCode    = λ γ → γ
            ; map-encode = λ _ → refl
            ; map-decode = λ _ → refl
            }
      ; mono∂ = λ le → le
      }

  assoc₁⁻¹ : K2.KernelHom₁ B A
  assoc₁⁻¹ =
    record
      { hom =
          record
            { con-hom    = idHom≡ (KH.conAlgOf A)
            ; mapCode    = λ γ → γ
            ; map-encode = λ _ → refl
            ; map-decode = λ _ → refl
            }
      ; mono∂ = λ le → le
      }

  assoc-invL : K2._≈_ (K2._∘₁_ assoc₁⁻¹ assoc₁) (K2.idKernelHom₁ A)
  assoc-invL =
    (λ _ → ConPreorder.refl (CP A))
    ,
    (λ _ → ConPreorder.refl (CP A))

  assoc-invR : K2._≈_ (K2._∘₁_ assoc₁ assoc₁⁻¹) (K2.idKernelHom₁ B)
  assoc-invR =
    (λ _ → ConPreorder.refl (CP B))
    ,
    (λ _ → ConPreorder.refl (CP B))

-- ============================================================================
-- 2) Satisfaction is literally precomposition under reindexKernel
-- ============================================================================

module ReindexingSatisfaction
  {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K₂ : Kernel Sig₂ Q)
  where

  open Reindex

  K₁ : Kernel Sig₁ Q
  K₁ = reindexKernel σ K₂

  module HT₁ = Truth.HomotypicalTruth Sig₁ Q (Kernel.HWorld K₁)
  module HT₂ = Truth.HomotypicalTruth Sig₂ Q (Kernel.HWorld K₂)
  module ST₁ = Truth.StrictTruth Sig₁
  module ST₂ = Truth.StrictTruth Sig₂

  SatH-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → HT₁.HLayer.Sat_H (Kernel.HTruth K₁) w c
      ≡ HT₂.HLayer.Sat_H (Kernel.HTruth K₂) (SigHom.mapCosp σ w) c
  SatH-precompose _ _ = refl

  SatS-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (φ : Kernel.Fml K₁)
    → ST₁.StrictLayer.Sat_S (Kernel.Strict K₁) w φ
      ≡ ST₂.StrictLayer.Sat_S (Kernel.Strict K₂) (SigHom.mapCosp σ w) φ
  SatS-precompose _ _ = refl

  SatHbnd-precompose
    : ∀ (w : LogOSSignature.∂Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → Kernel.Sat_H_bnd K₁ w c ≡ Kernel.Sat_H_bnd K₂ (SigHom.map∂Cosp σ w) c
  SatHbnd-precompose _ _ = refl

  SatHcoh-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → Prop._↔_
        (HT₁.HLayer.Sat_H (Kernel.HTruth K₁) w c)
        (Kernel.Sat_H_bnd K₁ (LogOSSignature.to∂ Sig₁ w) c)
  SatHcoh-precompose = Kernel.sat-coh K₁

module ReindexingSatisfactionWithFml
  {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K₂ : Kernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → Kernel.Fml K₂)
  where

  open Reindex

  K₁ : Kernel Sig₁ Q
  K₁ = reindexKernelWithFml σ K₂ mapFml

  module ST₁ = Truth.StrictTruth Sig₁
  module ST₂ = Truth.StrictTruth Sig₂
  module HT₁ = Truth.HomotypicalTruth Sig₁ Q (Kernel.HWorld K₁)
  module HT₂ = Truth.HomotypicalTruth Sig₂ Q (Kernel.HWorld K₂)

  SatS-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (φ : Fml₁)
    → Prop._↔_
        (ST₁.StrictLayer.Sat_S (Kernel.Strict K₁) w φ)
        (ST₂.StrictLayer.Sat_S (Kernel.Strict K₂) (SigHom.mapCosp σ w) (mapFml φ))
  SatS-precompose = reindexLogic-satS-withFml σ K₂ mapFml

  SatH-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → HT₁.HLayer.Sat_H (Kernel.HTruth K₁) w c
      ≡ HT₂.HLayer.Sat_H (Kernel.HTruth K₂) (SigHom.mapCosp σ w) c
  SatH-precompose _ _ = refl

  SatHbnd-precompose
    : ∀ (w : LogOSSignature.∂Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → Kernel.Sat_H_bnd K₁ w c ≡ Kernel.Sat_H_bnd K₂ (SigHom.map∂Cosp σ w) c
  SatHbnd-precompose _ _ = refl

  SatHcoh-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → Prop._↔_
        (HT₁.HLayer.Sat_H (Kernel.HTruth K₁) w c)
        (Kernel.Sat_H_bnd K₁ (LogOSSignature.to∂ Sig₁ w) c)
  SatHcoh-precompose = Kernel.sat-coh K₁

module ReindexingSatisfactionWithFmlLogic
  {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K₂ : LK.Kernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → LK.Kernel.Fml K₂)
  where

  open LK
  open Kernel

  K₁ : LK.Kernel Sig₁ Q
  K₁ = Reindex.reindexKernelWithFml σ K₂ mapFml

  module ST₁ = Truth.StrictTruth Sig₁
  module ST₂ = Truth.StrictTruth Sig₂
  module HT₁ = Truth.HomotypicalTruth Sig₁ Q (Kernel.HWorld K₁)
  module HT₂ = Truth.HomotypicalTruth Sig₂ Q (Kernel.HWorld K₂)

  SatS-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (φ : Fml₁)
    → Prop._↔_
        (ST₁.StrictLayer.Sat_S (Kernel.Strict K₁) w φ)
        (ST₂.StrictLayer.Sat_S (Kernel.Strict K₂) (SigHom.mapCosp σ w) (mapFml φ))
  SatS-precompose = Reindex.reindexLogic-satS-withFml σ K₂ mapFml

  SatH-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → HT₁.HLayer.Sat_H (Kernel.HTruth K₁) w c
      ≡ HT₂.HLayer.Sat_H (Kernel.HTruth K₂) (SigHom.mapCosp σ w) c
  SatH-precompose _ _ = refl

  SatHbnd-precompose
    : ∀ (w : LogOSSignature.∂Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → Kernel.Sat_H_bnd K₁ w c ≡ Kernel.Sat_H_bnd K₂ (SigHom.map∂Cosp σ w) c
  SatHbnd-precompose _ _ = refl

  SatHcoh-precompose
    : ∀ (w : LogOSSignature.Cosp Sig₁)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → Prop._↔_
        (HT₁.HLayer.Sat_H (Kernel.HTruth K₁) w c)
        (Kernel.Sat_H_bnd K₁ (LogOSSignature.to∂ Sig₁ w) c)
  SatHcoh-precompose = Kernel.sat-coh K₁

-- ============================================================================
-- 3) Kernel ↪ Kernel is 2-fully-faithful (by definitional restriction)
-- ============================================================================

module KernelIntoKernel
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  asKernel : Kernel Sig Q → Kernel Sig Q
  asKernel K = K

  toKernelHom₁
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → K2.KernelHom₁ K₁ K₂
    → K2.KernelHom₁ (asKernel K₁) (asKernel K₂)
  toKernelHom₁ h = h

  fromKernelHom₁
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → K2.KernelHom₁ (asKernel K₁) (asKernel K₂)
    → K2.KernelHom₁ K₁ K₂
  fromKernelHom₁ h = h

  to-from
    : ∀ {K₁ K₂ : Kernel Sig Q}
      (h : K2.KernelHom₁ K₁ K₂)
    → fromKernelHom₁ {K₁ = K₁} {K₂ = K₂} (toKernelHom₁ {K₁ = K₁} {K₂ = K₂} h) ≡ h
  to-from _ = refl

  from-to
    : ∀ {K₁ K₂ : Kernel Sig Q}
      (h : K2.KernelHom₁ (asKernel K₁) (asKernel K₂))
    → toKernelHom₁ {K₁ = K₁} {K₂ = K₂} (fromKernelHom₁ {K₁ = K₁} {K₂ = K₂} h) ≡ h
  from-to _ = refl

-- ============================================================================
-- 4) Refinement is compositional (congruence for ∘₁, and ≈-congruence)
-- ============================================================================

module RefinementLaws
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  open K2 public using
    ( _⇒_
    ; _≈_
    ; whiskerL
    ; whiskerR
    ; whisker-left
    ; whisker-right
    ; _⊙_
    ; cong-∘₁-≈
    ; trans⇒
    ; refl⇒
    ; refl≈
    ; trans≈
    ; sym≈
    )

-- ============================================================================
-- 5) Flow/Guard transport: steps are respected by flow-preserving morphisms (lax)
-- ============================================================================

module FlowGuardTransport
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  -- Kernel-hom flow preservation interface (saturation step).
  open KH public using (KernelHomFlow)

  -- Kernel version: a uniform “step semantics commutes with morphisms” lemma.
  map-guard-decode≤-Kernel
    : ∀ {K₁ K₂ : LK.Kernel Sig Q}
      {h : K2.KernelHom₁ K₁ K₂}
      (hf : K2.KernelHomFlow₁ h)
      (γ : LK.Kernel.Code K₁)
    → ConPreorder._⊑_ (BulkBoundary.bnd (LK.Kernel.BB K₂))
        (LK.Kernel.decode K₂ (K2.KernelHom₁.mapCode₁ h (LK.Kernel.Guard K₁ γ)))
        (LK.GTier.Flow (LK.Kernel.G K₂) (LK.GTier.step (LK.Kernel.G K₂))
          (LK.Kernel.decode K₂ (K2.KernelHom₁.mapCode₁ h γ)))
  map-guard-decode≤-Kernel {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
    let
      CP₂  = BulkBoundary.bnd (LK.Kernel.BB K₂)
      step₁ = LK.GTier.step (LK.Kernel.G K₁)
      step₂ = LK.GTier.step (LK.Kernel.G K₂)
      Flow₁ = LK.GTier.Flow (LK.Kernel.G K₁)
      Flow₂ = LK.GTier.Flow (LK.Kernel.G K₂)

      eq-guard₁ : LK.Kernel.decode K₁ (LK.Kernel.Guard K₁ γ)
                  ≡ Flow₁ step₁ (LK.Kernel.decode K₁ γ)
      eq-guard₁ = LK.Kernel.guard-decode K₁ γ

      eq-mapγ : LK.Kernel.decode K₂ (K2.KernelHom₁.mapCode₁ h γ)
                ≡ K2.KernelHom₁.map∂₁ h (LK.Kernel.decode K₁ γ)
      eq-mapγ = K2.KernelHom₁.map-decode₁ h γ

      eq-mapGuard : LK.Kernel.decode K₂ (K2.KernelHom₁.mapCode₁ h (LK.Kernel.Guard K₁ γ))
                    ≡ K2.KernelHom₁.map∂₁ h (LK.Kernel.decode K₁ (LK.Kernel.Guard K₁ γ))
      eq-mapGuard = K2.KernelHom₁.map-decode₁ h (LK.Kernel.Guard K₁ γ)

      step : ConPreorder._⊑_ CP₂
              (K2.KernelHom₁.map∂₁ h (Flow₁ step₁ (LK.Kernel.decode K₁ γ)))
              (Flow₂ step₂ (K2.KernelHom₁.map∂₁ h (LK.Kernel.decode K₁ γ)))
      step = K2.KernelHomFlow₁.preserves-step hf (LK.Kernel.decode K₁ γ)
    in
    subst
      (λ x → ConPreorder._⊑_ CP₂ x (Flow₂ step₂ (LK.Kernel.decode K₂ (K2.KernelHom₁.mapCode₁ h γ))))
      (sym eq-mapGuard)
      (subst
        (λ y → ConPreorder._⊑_ CP₂
                (K2.KernelHom₁.map∂₁ h (LK.Kernel.decode K₁ (LK.Kernel.Guard K₁ γ)))
                (Flow₂ step₂ y))
        (sym eq-mapγ)
        (subst
          (λ z → ConPreorder._⊑_ CP₂ (K2.KernelHom₁.map∂₁ h z)
                    (Flow₂ step₂ (K2.KernelHom₁.map∂₁ h (LK.Kernel.decode K₁ γ))))
          (sym eq-guard₁)
          step))
