{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Initial.FlowBase where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Adjunction using (MonoidalPoset)
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Algebra.ConAlg
open import LogOS.Kernel
open import LogOS.Kernel.Hom

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K₀ : Kernel Sig Q)
  where

  private
    module GT = Truth.GuardedTruth Sig Q
    I∂₀ = MonoidalPoset.I (Kernel.MBnd K₀)

  base-from-eq-bot
    : ∀ (K : Kernel Sig Q)
      (h : KernelHom K₀ K)
      (ωCPO : GT.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (eq-bot : ConAlgHom≡.map∂ (KernelHom.con-hom h) I∂₀ ≡ GT.OmegaCPO.⊥ ωCPO)
      (th⋆≡I∂ : GT.GuardedClosure.Th* (Kernel.GTruth K₀) ≡ I∂₀)
    → ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
        (ConAlgHom≡.map∂ (KernelHom.con-hom h)
          (GT.GuardedClosure.Th* (Kernel.GTruth K₀)))
        (GT.GuardedClosure.Th* (Kernel.GTruth K))
  base-from-eq-bot K h ωCPO eq-bot th⋆≡I∂ =
    let
      le : ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
             (GT.OmegaCPO.⊥ ωCPO)
             (GT.GuardedClosure.Th* (Kernel.GTruth K))
      le = GT.OmegaCPO.isBot ωCPO (GT.GuardedClosure.Th* (Kernel.GTruth K))

      eqTh : ConAlgHom≡.map∂ (KernelHom.con-hom h)
               (GT.GuardedClosure.Th* (Kernel.GTruth K₀))
             ≡ ConAlgHom≡.map∂ (KernelHom.con-hom h) I∂₀
      eqTh = cong (ConAlgHom≡.map∂ (KernelHom.con-hom h)) th⋆≡I∂

      eqBoth = trans eqTh eq-bot
    in
    subst
      (λ x → ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))) x
              (GT.GuardedClosure.Th* (Kernel.GTruth K)))
      (sym eqBoth) le
