{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Infinite.Initial where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.ConAlg
open import LogOS.Minimal.Constraints

open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.UngradedKernel.Hom
open import LogOS.Kernel.UngradedKernel.Initial as Init

open import LogOS.Kernel.UngradedKernel.Infinite
open import LogOS.Kernel.UngradedKernel.Infinite.Hom

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
        (∀ c → UngradedKernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) (UngradedKernel.encode K₀ c)
              ≡ UngradedKernelHom.mapCode (InfiniteKernelHom.hom h) (UngradedKernel.encode K₀ c))
        ×
        (∀ d → ConAlgHom≡.mapb (UngradedKernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK))) d
              ≡ ConAlgHom≡.mapb (UngradedKernelHom.con-hom (InfiniteKernelHom.hom h)) d)

    unique∞≃
      : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
        let IK₀ = Free∞
            K₀  = InfiniteKernel.K IK₀
            K   = InfiniteKernel.K IK
        in
        (∀ γ → UngradedKernel.decode K (UngradedKernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK))) (UngradedKernel.decode K₀ γ))
        ×
        (∀ γ → UngradedKernel.decode K (UngradedKernelHom.mapCode (InfiniteKernelHom.hom h) γ)
                ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom (InfiniteKernelHom.hom h)) (UngradedKernel.decode K₀ γ))
        ×
        (∀ γ → UngradedKernel.decode K (UngradedKernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                ≡ UngradedKernel.decode K (UngradedKernelHom.mapCode (InfiniteKernelHom.hom h) γ))

-- Build an initial infinite kernel from:
--  - a signature + QAdapter + chosen world (as for the finite initial kernel), and
--  - ωCPO/FiniteFirst structure on the free kernel’s boundary (plus bot≡I∂).

module Build∞ {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  private
    module GT∞ = Truth.GuardedTruth Sig Q

  build∞
    : (HW  : Worlds.WorldH Sig Q)
    → (poF   : BulkBoundaryPO (UngradedKernel.BB (Init.InitialKernel.FreeK (Init.build Sig Q HW))))
    → (ωCPOF : GT∞.OmegaCPO
                (BulkBoundary.bnd (UngradedKernel.BB (Init.InitialKernel.FreeK (Init.build Sig Q HW)))))
    → (FFF   : GT∞.FiniteFirst
                (BulkBoundary.bnd (UngradedKernel.BB (Init.InitialKernel.FreeK (Init.build Sig Q HW))))
                (UngradedKernel.GTruth (Init.InitialKernel.FreeK (Init.build Sig Q HW)))
                ωCPOF)
    → (bot≡I∂F : GT∞.OmegaCPO.⊥ ωCPOF
                 ≡ MonoidalOps.I (UngradedKernel.MBnd (Init.InitialKernel.FreeK (Init.build Sig Q HW))))
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

      FreeK : UngradedKernel Sig Q
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
          Kt : UngradedKernel Sig Q
          Kt = InfiniteKernel.K IK

          h : UngradedKernelHom FreeK Kt
          h = Init.InitialKernel.foldK IK₀ Kt

          eq-bot : ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h) I∂ ≡ GT∞.OmegaCPO.⊥ (InfiniteKernel.ωCPO IK)
          eq-bot =
            let unit∂ = ConAlgHom≡.unit∂ (UngradedKernelHom.con-hom h)
                bot≡I = InfiniteKernel.bot≡I∂ IK
            in trans unit∂ (sym bot≡I)

          ht : UngradedKernelHomFlow FreeK Kt h
          ht =
            ungradedKernelHomFlowOfStable
              (Init.foldFlow-build-auto Sig Q HW Kt (InfiniteKernel.ωCPO IK) eq-bot)

      unique∞
        : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
          (∀ c → UngradedKernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) (UngradedKernel.encode FreeK c)
                ≡ UngradedKernelHom.mapCode (InfiniteKernelHom.hom h) (UngradedKernel.encode FreeK c))
          ×
          (∀ d → ConAlgHom≡.mapb (UngradedKernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK))) d
                ≡ ConAlgHom≡.mapb (UngradedKernelHom.con-hom (InfiniteKernelHom.hom h)) d)
      unique∞ IK h = Init.InitialKernel.unique IK₀ (InfiniteKernel.K IK) (InfiniteKernelHom.hom h)

      unique∞≃
        : ∀ (IK : InfiniteKernel Sig Q) (h : InfiniteKernelHom Free∞ IK) →
          (∀ γ → UngradedKernel.decode (InfiniteKernel.K IK)
                  (UngradedKernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                  ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom (InfiniteKernelHom.hom (fold∞ IK)))
                                    (UngradedKernel.decode FreeK γ))
          ×
          (∀ γ → UngradedKernel.decode (InfiniteKernel.K IK)
                  (UngradedKernelHom.mapCode (InfiniteKernelHom.hom h) γ)
                  ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom (InfiniteKernelHom.hom h))
                                    (UngradedKernel.decode FreeK γ))
          ×
          (∀ γ → UngradedKernel.decode (InfiniteKernel.K IK)
                  (UngradedKernelHom.mapCode (InfiniteKernelHom.hom (fold∞ IK)) γ)
                  ≡ UngradedKernel.decode (InfiniteKernel.K IK)
                      (UngradedKernelHom.mapCode (InfiniteKernelHom.hom h) γ))
      unique∞≃ IK h = Init.InitialKernel.unique≃ IK₀ (InfiniteKernel.K IK) (InfiniteKernelHom.hom h)

build∞ = Build∞.build∞
