{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Initial.FlowBase where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.ConAlg
open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.UngradedKernel.Hom

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K₀ : UngradedKernel Sig Q)
  where

  private
    module GT = Truth.GuardedTruth Sig Q
    I∂₀ = MonoidalOps.I (UngradedKernel.MBnd K₀)

  base-from-eq-bot
    : ∀ (K : UngradedKernel Sig Q)
      (h : UngradedKernelHom K₀ K)
      (ωCPO : GT.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (eq-bot : ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h) I∂₀ ≡ GT.OmegaCPO.⊥ ωCPO)
      (th⋆≡I∂ : GT.GuardedClosure.Th* (UngradedKernel.GTruth K₀) ≡ I∂₀)
    → ConPreorder._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
        (ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h)
          (GT.GuardedClosure.Th* (UngradedKernel.GTruth K₀)))
        (GT.GuardedClosure.Th* (UngradedKernel.GTruth K))
  base-from-eq-bot K h ωCPO eq-bot th⋆≡I∂ =
    let
      le : ConPreorder._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
             (GT.OmegaCPO.⊥ ωCPO)
             (GT.GuardedClosure.Th* (UngradedKernel.GTruth K))
      le = GT.OmegaCPO.isBot ωCPO (GT.GuardedClosure.Th* (UngradedKernel.GTruth K))

      eqTh : ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h)
               (GT.GuardedClosure.Th* (UngradedKernel.GTruth K₀))
             ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h) I∂₀
      eqTh = cong (ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h)) th⋆≡I∂

      eqBoth = trans eqTh eq-bot
    in
    subst
      (λ x → ConPreorder._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))) x
              (GT.GuardedClosure.Th* (UngradedKernel.GTruth K)))
      (sym eqBoth) le
