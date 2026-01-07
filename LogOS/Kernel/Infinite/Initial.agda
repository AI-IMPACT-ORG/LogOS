{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Infinite.Initial where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalPoset)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Algebra.ConAlg
open import LogOS.Free.Constraints

open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Initial as Init

open import LogOS.Kernel.Infinite
open import LogOS.Kernel.Infinite.Hom

-- Initiality/canonicity for the *infinite* kernel upgrade.
--
-- We build an initial object “over” the existing initial kernel by equipping
-- its FreeK with ωCPO + FiniteFirst structure (and the canonical ⊥≡I∂ law).
--
-- Morphisms are the usual kernel homomorphisms together with Flow
-- preservation (`KernelHomFlow`). Uniqueness is inherited from the finite
-- initiality proof by forgetting the extra structure.

record InitialInfiniteKernel {ℓ : Level}
                             (Sig : LogOSSignature ℓ)
                             (Q   : QAdapter ℓ)
                             : Set (lsuc (lsuc ℓ)) where
  field
    Free∞ : InfiniteKernel Sig Q

    fold∞ : ∀ (IK : InfiniteKernel Sig Q) → InfiniteKernelHom Free∞ IK

    unique∞
      : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
        let IK₀ = Free∞
            K₀  = InfiniteKernel.K IK₀
            K   = InfiniteKernel.K IK
        in
        (∀ c → KernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) (Kernel.encode K₀ c)
              ≡ KernelHom.mapCode (InfiniteKernelHom.hom h) (Kernel.encode K₀ c))
        ×
        (∀ d → ConAlgHom≡.mapb (KernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK))) d
              ≡ ConAlgHom≡.mapb (KernelHom.con-hom (InfiniteKernelHom.hom h)) d)

    unique∞≃
      : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
        let IK₀ = Free∞
            K₀  = InfiniteKernel.K IK₀
            K   = InfiniteKernel.K IK
        in
        (∀ γ → Kernel.decode K (KernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                ≡ ConAlgHom≡.map∂ (KernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK))) (Kernel.decode K₀ γ))
        ×
        (∀ γ → Kernel.decode K (KernelHom.mapCode (InfiniteKernelHom.hom h) γ)
                ≡ ConAlgHom≡.map∂ (KernelHom.con-hom (InfiniteKernelHom.hom h)) (Kernel.decode K₀ γ))
        ×
        (∀ γ → Kernel.decode K (KernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                ≡ Kernel.decode K (KernelHom.mapCode (InfiniteKernelHom.hom h) γ))

-- Build an initial infinite kernel from:
--  - a signature + QAdapter + chosen world (as for the finite initial kernel), and
--  - ωCPO/FiniteFirst structure on the free kernel’s boundary (plus bot≡I∂).

module Build∞ {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  private
    module GT∞ = Truth.GuardedTruth Sig Q

  build∞
    : (HW  : Worlds.WorldH Sig Q)
    → (poF   : BulkBoundaryPO (Kernel.BB (Init.InitialKernel.FreeK (Init.build Sig Q HW))))
    → (ωCPOF : GT∞.OmegaCPO
                (BulkBoundary.bnd (Kernel.BB (Init.InitialKernel.FreeK (Init.build Sig Q HW)))))
    → (FFF   : GT∞.FiniteFirst
                (BulkBoundary.bnd (Kernel.BB (Init.InitialKernel.FreeK (Init.build Sig Q HW))))
                (Kernel.GTruth (Init.InitialKernel.FreeK (Init.build Sig Q HW)))
                ωCPOF)
    → (bot≡I∂F : GT∞.OmegaCPO.⊥ ωCPOF
                 ≡ MonoidalPoset.I (Kernel.MBnd (Init.InitialKernel.FreeK (Init.build Sig Q HW))))
    → InitialInfiniteKernel Sig Q
  build∞ HW poF ωCPOF FFF bot≡I∂F = record
    { Free∞ = Free∞
    ; fold∞ = fold∞
    ; unique∞ = unique∞
    ; unique∞≃ = unique∞≃
    }
    where
      IK₀ : Init.InitialKernel Sig Q
      IK₀ = Init.build Sig Q HW

      FreeK : Kernel Sig Q
      FreeK = Init.InitialKernel.FreeK IK₀

      Free∞ : InfiniteKernel Sig Q
      Free∞ = record
        { K = FreeK
        ; po = poF
        ; ωCPO = ωCPOF
        ; FF = FFF
        ; bot≡I∂ = bot≡I∂F
        }

      fold∞ : ∀ (IK : InfiniteKernel Sig Q) → InfiniteKernelHom Free∞ IK
      fold∞ IK = record { hom = h ; flow = ht }
        where
          Kt : Kernel Sig Q
          Kt = InfiniteKernel.K IK

          h : KernelHom FreeK Kt
          h = Init.InitialKernel.foldK IK₀ Kt

          eq-bot : ConAlgHom≡.map∂ (KernelHom.con-hom h) I∂ ≡ GT∞.OmegaCPO.⊥ (InfiniteKernel.ωCPO IK)
          eq-bot =
            let unit∂ = ConAlgHom≡.unit∂ (KernelHom.con-hom h)
                bot≡I = InfiniteKernel.bot≡I∂ IK
            in trans unit∂ (sym bot≡I)

          ht : KernelHomFlow FreeK Kt h
          ht = Init.foldFlow-build-auto Sig Q HW Kt (InfiniteKernel.ωCPO IK) eq-bot

      unique∞
        : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
          (∀ c → KernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) (Kernel.encode FreeK c)
                ≡ KernelHom.mapCode (InfiniteKernelHom.hom h) (Kernel.encode FreeK c))
          ×
          (∀ d → ConAlgHom≡.mapb (KernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK))) d
                ≡ ConAlgHom≡.mapb (KernelHom.con-hom (InfiniteKernelHom.hom h)) d)
      unique∞ IK h = Init.InitialKernel.unique IK₀ (InfiniteKernel.K IK) (InfiniteKernelHom.hom h)

      unique∞≃
        : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
          (∀ γ → Kernel.decode (InfiniteKernel.K IK)
                  (KernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                  ≡ ConAlgHom≡.map∂ (KernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK)))
                                    (Kernel.decode FreeK γ))
          ×
          (∀ γ → Kernel.decode (InfiniteKernel.K IK)
                  (KernelHom.mapCode (InfiniteKernelHom.hom h) γ)
                  ≡ ConAlgHom≡.map∂ (KernelHom.con-hom (InfiniteKernelHom.hom h))
                                    (Kernel.decode FreeK γ))
          ×
          (∀ γ → Kernel.decode (InfiniteKernel.K IK)
                  (KernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                  ≡ Kernel.decode (InfiniteKernel.K IK)
                      (KernelHom.mapCode (InfiniteKernelHom.hom h) γ))
      unique∞≃ IK h = Init.InitialKernel.unique≃ IK₀ (InfiniteKernel.K IK) (InfiniteKernelHom.hom h)

build∞ = Build∞.build∞
