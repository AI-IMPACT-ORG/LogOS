{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureBulkBoundary2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Bulk-boundary law over the architectural boundary basis `LOGᴳ`.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; refl⊑)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Theorems.AbstractGaloisConnection as Galois using (GaloisConnection)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.LOG.Boundary2Cat using (LOGᴳ; map∂; map∂-mono)

private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data BulkBoundaryTag : Set where
  bulkBoundaryTag : BulkBoundaryTag

bulkBoundaryTagId : ℕ
bulkBoundaryTagId = 24

record BulkBoundaryEconomy
  {ℓ ℓRel ℓCode : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  : Set (lsuc (ℓ ⊔ ℓRel)) where
  field
    ext : ConPreorder ℓ ℓRel
    ext⟂bnd : GaloisConnection (bnd K) ext

open BulkBoundaryEconomy public

flowFromBulk
  : ∀ {ℓ ℓRel ℓCode}
    {K : Kernel ℓ ℓRel ℓCode}
  → BulkBoundaryEconomy K → GuardedClosure (bnd K)
flowFromBulk {K = K} E =
  Galois.closure (BulkBoundaryEconomy.ext⟂bnd E)

BulkBoundaryDisplayedᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOGᴳ {ℓ} {ℓRel} {ℓCode}) (lsuc (ℓ ⊔ ℓRel)) (ℓ ⊔ ℓRel)
BulkBoundaryDisplayedᴳ {ℓ} {ℓRel} {ℓCode} =
  let
    C = LOGᴳ {ℓ} {ℓRel} {ℓCode}
    module C = Thin2Cat C
  in
  record
    { Ob = λ K → BulkBoundaryEconomy {ℓ = ℓ} {ℓRel = ℓRel} {ℓCode = ℓCode} K
    ; HomD =
        λ {K} {K'} (h : Con (C.Hom K K'))
          (E : BulkBoundaryEconomy K)
          (E' : BulkBoundaryEconomy K')
        → ∀ c
        → _⊑_ (bnd K')
            (map∂ h (Flow (flowFromBulk E) c))
            (Flow (flowFromBulk E') (map∂ h c))
    ; idD = λ {K} E c → refl⊑ (bnd K)
    ; compD =
        λ {K₁} {K₂} {K₃} {h} {k} {E₁} {E₂} {E₃} compat₁₂ compat₂₃ c →
          let
            module R = ≤-Reasoning (bnd K₃)
            open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
          in
          begin⊑
            map∂ k (map∂ h (Flow (flowFromBulk E₁) c)) ⊑⟨ map∂-mono k (compat₁₂ c) ⟩
            map∂ k (Flow (flowFromBulk E₂) (map∂ h c)) ⊑⟨ compat₂₃ (map∂ h c) ⟩
            Flow (flowFromBulk E₃) (map∂ k (map∂ h c)) ∎⊑
    }

module Port {ℓ ℓRel ℓCode : Level} =
  Template.SingletonLayer
    bulkBoundaryTagId
    {Tag = BulkBoundaryTag}
    (BulkBoundaryDisplayedᴳ {ℓ} {ℓRel} {ℓCode})

bulkBoundarySigᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOGᴳ {ℓ} {ℓRel} {ℓCode}) bulkBoundaryTagId BulkBoundaryTag
bulkBoundarySigᴳ {ℓ} {ℓRel} {ℓCode} =
  Port.portSig {ℓ} {ℓRel} {ℓCode}

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)
