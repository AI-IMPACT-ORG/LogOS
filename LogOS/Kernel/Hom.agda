{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom where

open import LogOS.Prelude

open import LogOS.Kernel
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Truth as Truth

-- Extract the constraint algebra from a Kernel.

conAlgOf : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           → Kernel Sig Q → ConAlg {ℓ}
conAlgOf K = record { BB = Kernel.BB K ; MBulk = Kernel.MBulk K ; MBnd = Kernel.MBnd K ; Holo = Kernel.Holo K }

-- Kernel morphism: preserves the constraint algebra (strictly) and code coherence.

record KernelHom {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q : QAdapter ℓ}
                 (K₁ K₂ : Kernel Sig Q)
                 : Set (lsuc (lsuc ℓ)) where
  open Kernel K₁ renaming (BB to BB₁; MBulk to MBulk₁; MBnd to MBnd₁; Holo to Holo₁; Code to Code₁; encode to encode₁; decode to decode₁)
  open Kernel K₂ renaming (BB to BB₂; MBulk to MBulk₂; MBnd to MBnd₂; Holo to Holo₂; Code to Code₂; encode to encode₂; decode to decode₂)
  field
    con-hom : ConAlgHom≡ (conAlgOf K₁) (conAlgOf K₂)
    mapCode : Code₁ → Code₂
    -- Code coherence with constraints
    map-encode : ∀ c → mapCode (encode₁ c) ≡ encode₂ (ConAlgHom≡.map∂ con-hom c)
    map-decode : ∀ γ → decode₂ (mapCode γ) ≡ ConAlgHom≡.map∂ con-hom (decode₁ γ)
    -- Note: `FlowCode` naturality is model-specific and omitted here

  -- Up-to-decode equality on code maps (helpful for quotiented initiality)
  infix 4 _≈Code_
  _≈Code_ : Code₁ → Code₁ → Set ℓ
  _≈Code_ γ δ = decode₁ γ ≡ decode₁ δ


-- Identity and composition for KernelHom.

idKernelHom : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) → KernelHom K K
idKernelHom K = record
  { con-hom   = idHom≡ (conAlgOf K)
  ; mapCode   = λ γ → γ
  ; map-encode = λ c → refl
  ; map-decode = λ γ → refl
  }

composeKernelHom : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} {K₁ K₂ K₃ : Kernel Sig Q}
                  → KernelHom K₁ K₂ → KernelHom K₂ K₃ → KernelHom K₁ K₃
composeKernelHom h₁ h₂ = record
  { con-hom   = composeHom≡ (KernelHom.con-hom h₁) (KernelHom.con-hom h₂)
  ; mapCode   = λ γ → KernelHom.mapCode h₂ (KernelHom.mapCode h₁ γ)
  ; map-encode = λ c → trans
                    (cong (KernelHom.mapCode h₂) (KernelHom.map-encode h₁ c))
                    (KernelHom.map-encode h₂ (ConAlgHom≡.map∂ (KernelHom.con-hom h₁) c))
  ; map-decode = λ γ → trans
                    (KernelHom.map-decode h₂ (KernelHom.mapCode h₁ γ))
                    (cong (ConAlgHom≡.map∂ (KernelHom.con-hom h₂)) (KernelHom.map-decode h₁ γ))
  }

-- Derived coherence for reify at decode-level under a KernelHom.

map-reify-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    (γ : Kernel.Code K₁)
  → Kernel.decode K₂ (KernelHom.mapCode h (Kernel.reify K₁ γ))
    ≡ ConAlgHom≡.map∂ (KernelHom.con-hom h) (Kernel.decode K₁ γ)
map-reify-decode {K₁ = K₁} {K₂ = K₂} h γ =
  let open KernelHom h in
  trans (map-decode (Kernel.reify K₁ γ)) (cong (ConAlgHom≡.map∂ con-hom) (Kernel.reify-decode K₁ γ))

-- Decode of mapped `Body`, via the boundary body `Body∂`.

map-body-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    (γ : Kernel.Code K₁)
  → Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Body K₁ γ))
    ≡ ConAlgHom≡.map∂ (KernelHom.con-hom h) (Kernel.Body∂ K₁ (Kernel.decode K₁ γ))
map-body-decode {K₁ = K₁} {K₂ = K₂} h γ =
  let open KernelHom h in
  trans (map-decode (Kernel.Body K₁ γ)) (cong (ConAlgHom≡.map∂ con-hom) (Kernel.body-decode K₁ γ))

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
    flow-hom : (let module GT' = Truth.GuardedTruth Sig Q in GT'.FlowHom)
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
      ((let module GT = Truth.GuardedTruth Sig Q in GT.GuardedClosure.Flow (Kernel.GTruth K₂))
        (Kernel.decode K₂ (KernelHom.mapCode h γ)))
map-guard-decode≤ {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  let open KernelHom h
      module GT = Truth.GuardedTruth Sig Q
      open GT.FlowHom (KernelHomFlow.flow-hom hf) using (preserves-F)
      CP₂ = BulkBoundary.bnd (Kernel.BB K₂)
      Flow₁ = GT.GuardedClosure.Flow (Kernel.GTruth K₁)
      Flow₂ = GT.GuardedClosure.Flow (Kernel.GTruth K₂)
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
      ((let module GT = Truth.GuardedTruth Sig Q in GT.GuardedClosure.Flow (Kernel.GTruth K₂))
        (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Body K₁ γ))))
map-flowcode-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  map-guard-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf (Kernel.Body K₁ γ)
