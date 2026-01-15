{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
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
import LogOS.Kernel.Initial.FlowBase as FlowBase

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
  Strict₀ = record { Sat_S = λ _ _ → Topℓ }
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
    { shape = record
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
        ; Code   = Code₀
        ; encode = encode₀
        ; decode = decode₀
        ; Guard         = Guard₀
        ; Body          = Body₀
        ; γ*            = I∂
        ; reify         = λ γ → encode₀ (decode₀ γ)
        ; Body∂         = λ c → decode₀ (Body₀ (encode₀ c))
        }
    ; GTruth       = GTruth₀
    ; laws = record
        { shapeLaws = record
            { decode∘encode = λ _ → refl
            ; γ*-guard =
                (ConPoset.refl (BulkBoundary.bnd BB₀) {c = decode₀ I∂})
              , (ConPoset.refl (BulkBoundary.bnd BB₀) {c = decode₀ I∂})
            ; reify-decode  = λ _ → refl
            ; body-decode   = λ _ → refl
            }
        ; mono-Body∂    = λ {c} {d} le → le
        ; mono-Flow     = Truth.GuardedCore.GuardedClosure.mono GTruth₀
        ; guard-decode  = λ _ → refl
        ; decode-γ*     = refl
        }
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
            GT₀.GuardedClosure.infl (Kernel.GTruth K)
              (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) c)
        ; preserves-Th = base
        }
    }

  -- Automatic construction of the base inequality using OmegaCPO + FiniteFirst
  foldFlow-auto
    : ∀ (K : Kernel Sig Q)
      (ωCPO : GT₀.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (eq-bot : ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) I∂ ≡ GT₀.OmegaCPO.⊥ ωCPO)
      → KernelHomFlow freeK K (foldHom K)
  foldFlow-auto K ωCPO eq-bot = foldFlow K base
    where
      module FB = FlowBase.For freeK
      base : ConPoset._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
               (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (GT₀.GuardedClosure.Th* GTruth₀))
               (GT₀.GuardedClosure.Th* (Kernel.GTruth K))
      base = FB.base-from-eq-bot K (foldHom K) ωCPO eq-bot refl

  -- Variant: base via inequality map∂ I∂ ⊑ ⊥
  foldFlow-auto-ineq
    : ∀ (K : Kernel Sig Q)
      (ωCPO : GT₀.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
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

module FoldFlowBuildAuto {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  private
    module GT = Truth.GuardedTruth Sig Q

  foldFlow-build-auto
    : (HWorld : Worlds.WorldH Sig Q)
    → (K : Kernel Sig Q)
    → (ωCPO : GT.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
    → (eq-bot : ConAlgHom≡.map∂ (KernelHom.con-hom (InitialKernel.foldK (build Sig Q HWorld) K)) I∂
                ≡ GT.OmegaCPO.⊥ ωCPO)
    → KernelHomFlow (InitialKernel.FreeK (build Sig Q HWorld)) K
        (InitialKernel.foldK (build Sig Q HWorld) K)
  foldFlow-build-auto HW K ωCPO eq-bot =
    let IK   = build Sig Q HW
        h    = InitialKernel.foldK IK K
        module FB = FlowBase.For (InitialKernel.FreeK IK)
        base = FB.base-from-eq-bot K h ωCPO eq-bot refl
    in record
      { flow-hom = record
          { preserves-F  = λ c →
              GT.GuardedClosure.infl (Kernel.GTruth K)
                (ConAlgHom≡.map∂ (KernelHom.con-hom h) c)
          ; preserves-Th = base
          }
      }

foldFlow-build-auto = FoldFlowBuildAuto.foldFlow-build-auto
