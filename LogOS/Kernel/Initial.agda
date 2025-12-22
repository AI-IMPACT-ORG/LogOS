{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Initial where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Algebra.ConAlg
open import LogOS.Free.Constraints
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Kernel.Hom

-- Free/initial Kernel over a fixed signature + QAdapter.

record InitialKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) : Set (lsuc (lsuc ℓ)) where
  module W = Worlds Sig
  field
    FreeK  : Kernel Sig Q
    foldK  : ∀ (K : Kernel Sig Q) → KernelHom FreeK K
    unique : ∀ (K : Kernel Sig Q) (h : KernelHom FreeK K) →
             (∀ c → KernelHom.mapCode (foldK K) (Kernel.encode FreeK c) ≡ KernelHom.mapCode h (Kernel.encode FreeK c)) ×
             (∀ d → ConAlgHom≡.mapb (KernelHom.con-hom (foldK K)) d ≡ ConAlgHom≡.mapb (KernelHom.con-hom h) d)
    -- Up-to-decode uniqueness on all codes (quotiented morphism view)
    unique≃ : ∀ (K : Kernel Sig Q) (h : KernelHom FreeK K) →
              (∀ γ → Kernel.decode K (KernelHom.mapCode (foldK K) γ)
                      ≡ ConAlgHom≡.map∂ (KernelHom.con-hom (foldK K)) (Kernel.decode FreeK γ)) ×
              (∀ γ → Kernel.decode K (KernelHom.mapCode h γ)
                      ≡ ConAlgHom≡.map∂ (KernelHom.con-hom h) (Kernel.decode FreeK γ)) ×
              (∀ γ → Kernel.decode K (KernelHom.mapCode (foldK K) γ)
                      ≡ Kernel.decode K (KernelHom.mapCode h γ))

-- Construction: minimal world, free constraints, trivial truth, code-as-constraints

build : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) (HWorld₀ : Worlds.WorldH Sig Q) → InitialKernel Sig Q
build {ℓ} Sig Q HWorld₀ = record
    { FreeK = freeK
    ; foldK = λ K → foldHom K
    ; unique = λ K h →
        let eq∂ , eqb = InitialConAlg.unique initialConAlg (conAlgOf K) (KernelHom.con-hom h)
        in (λ c →
              trans
                (KernelHom.map-encode (foldHom K) c)
                (trans
                   (cong (λ x → Kernel.encode K x) (eq∂ c))
                   (sym (KernelHom.map-encode h c))))
           ,
           (λ d → eqb d)
    ; unique≃ = λ K h →
        let eq∂ , _ = InitialConAlg.unique initialConAlg (conAlgOf K) (KernelHom.con-hom h)
        in (λ γ → KernelHom.map-decode (foldHom K) γ)
           , (λ γ → KernelHom.map-decode h γ)
           , (λ γ →
                trans (KernelHom.map-decode (foldHom K) γ)
                      (trans (eq∂ (Kernel.decode freeK γ))
                             (sym (KernelHom.map-decode h γ))))
    }
  where
  module W = Worlds Sig
  open LogOSSignature Sig

  -- Use shared universe-polymorphic unit alias from Prelude
  -- `Topℓ` is already available from `LogOS.Prelude`.

  -- Use free constraint algebra
  BB₀    = ConAlg.BB FreeConAlg
  MBulk₀ = ConAlg.MBulk FreeConAlg
  MBnd₀  = ConAlg.MBnd FreeConAlg
  Holo₀  = ConAlg.Holo FreeConAlg

  -- H-tier truth (trivial, always satisfied)
  module HT₀ = Truth.HomotypicalTruth Sig Q HWorld₀
  HTruth₀ : HT₀.HLayer BB₀
  HTruth₀ = record
    { Sat_H   = λ _ _ → Topℓ
    ; mono-Con = λ _ x → x
    ; mono-ctx = λ _ x → x
    }

  HInv₀ : HT₀.Invariance BB₀
  HInv₀ = record
    { Inv_H = λ c → c
    ; infl  = λ c → ConPoset.refl (BulkBoundary.bnd BB₀)
    ; idemp-lax = λ c → ConPoset.refl (BulkBoundary.bnd BB₀)
    }

  -- S-tier: trivial strict layer
  Fml₀ : Set ℓ
  Fml₀ = Topℓ
  module ST₀ = Truth.StrictTruth Sig
  Strict₀ : ST₀.StrictLayer Fml₀
  Strict₀ = record { Sat_S = λ _ _ → Topℓ ; _⊢S_ = λ _ _ → Topℓ }
  TransH₀ : Fml₀ → ConPoset.Con (BulkBoundary.bnd BB₀)
  TransH₀ = λ _ → I∂

  -- G-tier: trivial closure and fixed point
  module GT₀ = Truth.GuardedTruth Sig Q
  GTruth₀ : GT₀.GuardedClosure (BulkBoundary.bnd BB₀)
  GTruth₀ = record
    { Flow = λ c → c
    ; mono = λ p → p
    ; infl = λ c → ConPoset.refl (BulkBoundary.bnd BB₀)
    ; idemp-lax = λ c → ConPoset.refl (BulkBoundary.bnd BB₀)
    ; Th* = I∂
    ; Th*-fixed = ( ConPoset.refl (BulkBoundary.bnd BB₀) , ConPoset.refl (BulkBoundary.bnd BB₀) )
    }

  -- Code layer as constraints
  Code₀ : Set ℓ
  Code₀ = ConPoset.Con (BulkBoundary.bnd BB₀)
  encode₀ : ConPoset.Con (BulkBoundary.bnd BB₀) → Code₀
  encode₀ = λ c → c
  decode₀ : Code₀ → ConPoset.Con (BulkBoundary.bnd BB₀)
  decode₀ = λ γ → γ
  Guard₀ : Code₀ → Code₀
  Guard₀ = λ γ → encode₀ (GT₀.GuardedClosure.Flow GTruth₀ (decode₀ γ))
  Body₀ : Code₀ → Code₀
  Body₀ = λ γ → γ

  freeK : Kernel Sig Q
  freeK = record
    { HWorld = HWorld₀
    ; BB     = BB₀
    ; MBulk  = MBulk₀
    ; MBnd   = MBnd₀
    ; Holo   = Holo₀
    ; HTruth = HTruth₀
    ; HInv   = HInv₀
    ; Sat_H_bnd = λ _ _ → Topℓ
    ; sat-coh   = λ _ _ → record { to = λ x → x ; from = λ x → x }
    ; Fml = Fml₀
    ; Strict = Strict₀
    ; TransH = TransH₀
    ; coh-LH = λ _ _ → record { to = λ x → x ; from = λ x → x }
    ; GTruth = GTruth₀
    ; Code   = Code₀
    ; encode = encode₀
    ; decode = decode₀
    ; decode∘encode = λ _ → refl
    ; Guard         = Guard₀
    ; Body          = Body₀
    ; guard-decode  = λ _ → refl
    ; γ*            = I∂
    ; γ*-guard      =
        (ConPoset.refl (BulkBoundary.bnd BB₀) {c = decode₀ I∂})
      , (ConPoset.refl (BulkBoundary.bnd BB₀) {c = decode₀ I∂})
    ; decode-γ*     = refl
    ; reify         = λ γ → encode₀ (decode₀ γ)
    ; reify-decode  = λ γ → refl
    ; Body∂         = λ c → decode₀ (Body₀ (encode₀ c))
    ; body-decode   = λ γ → refl
    }

  -- Canonical fold hom into any Kernel K: constraints via initialConAlg, code by encode∘map∂∘decode
  foldHom : ∀ (K : Kernel Sig Q) → KernelHom freeK K
  foldHom K = record
    { con-hom   = fold≡ (conAlgOf K)
    ; mapCode   = λ γ → Kernel.encode K (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (Kernel.decode freeK γ))
    ; map-encode = λ c → cong (λ x → Kernel.encode K (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) x)) (Kernel.decode∘encode freeK c)
    ; map-decode = λ γ → Kernel.decode∘encode K (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (Kernel.decode freeK γ))
    }

  -- Optional promotion: Flow-preserving hom (KernelHomFlow) from FreeK to any K
  -- Requires only the inflation law at K for preserves-F; preserves-Th needs a base lemma
  foldFlow : ∀ (K : Kernel Sig Q)
           → (base : ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
                                   (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (GT₀.GuardedClosure.Th* GTruth₀))
                                   (Th⋆K K))
           → KernelHomFlow freeK K (foldHom K)
  foldFlow K base = record
    { flow-hom = record
        { preserves-F  = λ c →
            (let module GT = Truth.GuardedTruth Sig Q in GT.GuardedClosure.infl (Kernel.GTruth K))
              (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) c)
        ; preserves-Th = base
        }
    }

  -- Automatic construction of the base inequality using OmegaCPO + FiniteFirst
  foldFlow-auto
    : ∀ (K : Kernel Sig Q)
      (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (eq-bot : ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) I∂ ≡ GT₀.OmegaCPO.⊥ ωCPO)
      → KernelHomFlow freeK K (foldHom K)
  foldFlow-auto K ωCPO eq-bot = foldFlow K base
    where
      -- base: map∂ Th*₀ = map∂ I∂ ≡ ⊥ ≤ Th*K
      base : ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
                           (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (GT₀.GuardedClosure.Th* GTruth₀))
                           (GT₀.GuardedClosure.Th* (Kernel.GTruth K))
      base =
        let le : ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))) (GT₀.OmegaCPO.⊥ ωCPO) (GT₀.GuardedClosure.Th* (Kernel.GTruth K))
            le = GT₀.OmegaCPO.isBot ωCPO (GT₀.GuardedClosure.Th* (Kernel.GTruth K))
            eqTh : ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (GT₀.GuardedClosure.Th* GTruth₀)
                   ≡ ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) I∂
            eqTh = refl
            eqBoth = trans eqTh eq-bot
        in subst (λ x → ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))) x (GT₀.GuardedClosure.Th* (Kernel.GTruth K)))
                 (sym eqBoth) le

  -- Variant: base via inequality map∂ I∂ ⊑ ⊥
  foldFlow-auto-ineq
    : ∀ (K : Kernel Sig Q)
      (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (le-bot : ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
                              (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) I∂)
                              (GT₀.OmegaCPO.⊥ ωCPO))
      → KernelHomFlow freeK K (foldHom K)
  foldFlow-auto-ineq K ωCPO le-bot = foldFlow K base
    where
      base =
        ConPoset.trans
          (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
          le-bot
          (GT₀.OmegaCPO.isBot ωCPO (GT₀.GuardedClosure.Th* (Kernel.GTruth K)))

-- Top-level convenience: construct a Flow-preserving hom (KernelHomFlow)
-- from the initial kernel built at (Sig, Q, HWorld).

foldFlow-build-auto
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (HWorld : Worlds.WorldH Sig Q)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
    (eq-bot : ConAlgHom≡.map∂ (KernelHom.con-hom (InitialKernel.foldK (build Sig Q HWorld) K)) I∂
              ≡ (let module GT0 = Truth.GuardedTruth Sig Q in GT0.OmegaCPO.⊥ ωCPO))
  → KernelHomFlow (InitialKernel.FreeK (build Sig Q HWorld)) K (InitialKernel.foldK (build Sig Q HWorld) K)
foldFlow-build-auto Sig Q HW K ωCPO eq-bot =
  let IK   = build Sig Q HW
      h    = InitialKernel.foldK IK K
      bb   = ConAlg.BB (conAlgOf K)
      le   = (let module GT0 = Truth.GuardedTruth Sig Q in GT0.OmegaCPO.isBot ωCPO) (Th⋆K K)
      eqTh = refl
      eqBoth = trans eqTh eq-bot
      base = subst (λ x → ConPoset._⊑_ (BulkBoundary.bnd bb) x (Th⋆K K)) (sym eqBoth) le
  in record
    { flow-hom = record
        { preserves-F  = λ c →
            (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.infl (Kernel.GTruth K))
              (ConAlgHom≡.map∂ (KernelHom.con-hom h) c)
        ; preserves-Th = base
        }
    }
