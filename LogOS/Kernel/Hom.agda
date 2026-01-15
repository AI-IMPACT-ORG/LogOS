{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom where

open import LogOS.Prelude

open import LogOS.Kernel
open import LogOS.Kernel.ConAlgOf public using (conAlgOf)
open import LogOS.Kernel.HomCore as HomCore
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Truth as Truth

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : HomCore.Ops {ℓ}
    ops =
      record
        { Obj          = Kernel Sig Q
        ; conAlgOf     = conAlgOf
        ; Code         = Kernel.Code
        ; encode       = Kernel.encode
        ; decode       = Kernel.decode
        ; reify        = Kernel.reify
        ; reify-decode = Kernel.reify-decode
        ; Body         = Kernel.Body
        ; Body∂        = Kernel.Body∂
        ; body-decode  = Kernel.body-decode
        }

  open HomCore.WithOps ops public
    renaming
      ( Hom            to KernelHom
      ; idHom          to idKernelHom
      ; composeHom     to composeKernelHom
      ; map-reify-decode to map-reify-decode
      ; map-body-decode  to map-body-decode
      )

  map∂-id
    : ∀ {K} (c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
    → ConAlgHom≡.map∂ (KernelHom.con-hom (idKernelHom K)) c ≡ c
  map∂-id _ = refl

  map∂-compose
    : ∀ {K₁ K₂ K₃}
      (h₁ : KernelHom K₁ K₂)
      (h₂ : KernelHom K₂ K₃)
      (c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K₁)))
    → ConAlgHom≡.map∂ (KernelHom.con-hom (composeKernelHom h₁ h₂)) c
      ≡ ConAlgHom≡.map∂ (KernelHom.con-hom h₂) (ConAlgHom≡.map∂ (KernelHom.con-hom h₁) c)
  map∂-compose _ _ _ = refl

  mapCode-id
    : ∀ {K} (γ : Kernel.Code K)
    → KernelHom.mapCode (idKernelHom K) γ ≡ γ
  mapCode-id _ = refl

  mapCode-compose
    : ∀ {K₁ K₂ K₃}
      (h₁ : KernelHom K₁ K₂)
      (h₂ : KernelHom K₂ K₃)
      (γ : Kernel.Code K₁)
    → KernelHom.mapCode (composeKernelHom h₁ h₂) γ
      ≡ KernelHom.mapCode h₂ (KernelHom.mapCode h₁ γ)
  mapCode-compose _ _ _ = refl

-- Optional strengthening: preservation of Flow and Th* on boundary constraints.

record KernelHomFlow {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q : QAdapter ℓ}
                     (K₁ K₂ : Kernel Sig Q)
                     (h : KernelHom K₁ K₂)
                     : Set (lsuc (lsuc ℓ)) where
  open Kernel K₁ renaming (BB to BB₁; GTruth to G₁)
  open Kernel K₂ renaming (BB to BB₂; GTruth to G₂)
  open KernelHom h
  field
    flow-hom
      : Truth.GuardedCore.FlowHom
          (BulkBoundary.bnd BB₁)
          (BulkBoundary.bnd BB₂)
          G₁ G₂
          (ConAlgHom≡.map∂ con-hom)

-- Decode-level transport for Guard/FlowCode under Flow-preserving homs (lax).

map-guard-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    {h : KernelHom K₁ K₂}
    (hf : KernelHomFlow K₁ K₂ h)
    (γ : Kernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
      (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Guard K₁ γ)))
      (Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K₂)
        (Kernel.decode K₂ (KernelHom.mapCode h γ)))
map-guard-decode≤ {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  let open KernelHom h
      open Truth.GuardedCore.FlowHom (KernelHomFlow.flow-hom hf) using (preserves-F)
      CP₂ = BulkBoundary.bnd (Kernel.BB K₂)
      Flow₁ = Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K₁)
      Flow₂ = Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K₂)
      eqL = trans (map-decode (Kernel.Guard K₁ γ))
                  (cong (ConAlgHom≡.map∂ con-hom) (Kernel.guard-decode K₁ γ))
      eqR = map-decode γ
      step = subst
               (λ x → ConPoset._⊑_ CP₂
                        (ConAlgHom≡.map∂ con-hom (Flow₁ (Kernel.decode K₁ γ)))
                        (Flow₂ x))
               (sym eqR)
               (preserves-F (Kernel.decode K₁ γ))
  in subst
       (λ x → ConPoset._⊑_ CP₂ x (Flow₂ (Kernel.decode K₂ (mapCode γ))))
       (sym eqL)
       step

map-flowcode-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    {h : KernelHom K₁ K₂}
    (hf : KernelHomFlow K₁ K₂ h)
    (γ : Kernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
      (Kernel.decode K₂ (KernelHom.mapCode h (FlowCode K₁ γ)))
      (Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K₂)
        (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Body K₁ γ))))
map-flowcode-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  map-guard-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf (Kernel.Body K₁ γ)
