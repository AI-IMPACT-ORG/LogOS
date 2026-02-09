{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Initial where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.ConAlg
open import LogOS.Minimal.Constraints
open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.UngradedKernel.Endo
open import LogOS.Kernel.UngradedKernel.Hom
import LogOS.Kernel.UngradedKernel.Initial.FlowBase as FlowBase

-- Free/initial UngradedKernel over a fixed signature + QAdapter.

record InitialKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) : Set (lsuc (lsuc ℓ)) where
  module W = Worlds Sig
  field
    FreeK  : UngradedKernel Sig Q
    foldK  : ∀ (K : UngradedKernel Sig Q) → UngradedKernelHom FreeK K
    unique : ∀ (K : UngradedKernel Sig Q) (h : UngradedKernelHom FreeK K) →
             (∀ c → UngradedKernelHom.mapCode (foldK K) (UngradedKernel.encode FreeK c) ≡ UngradedKernelHom.mapCode h (UngradedKernel.encode FreeK c)) ×
             (∀ d → ConAlgHom≡.mapb (UngradedKernelHom.con-hom (foldK K)) d ≡ ConAlgHom≡.mapb (UngradedKernelHom.con-hom h) d)
    -- Up-to-decode uniqueness on all codes (quotiented morphism view)
    unique≃ : ∀ (K : UngradedKernel Sig Q) (h : UngradedKernelHom FreeK K) →
              (∀ γ → UngradedKernel.decode K (UngradedKernelHom.mapCode (foldK K) γ)
                      ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom (foldK K)) (UngradedKernel.decode FreeK γ)) ×
              (∀ γ → UngradedKernel.decode K (UngradedKernelHom.mapCode h γ)
                      ≡ ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h) (UngradedKernel.decode FreeK γ)) ×
              (∀ γ → UngradedKernel.decode K (UngradedKernelHom.mapCode (foldK K) γ)
                      ≡ UngradedKernel.decode K (UngradedKernelHom.mapCode h γ))

-- Construction: minimal world, free constraints, trivial truth, code-as-constraints

build : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) (HWorld₀ : Worlds.WorldH Sig Q) → InitialKernel Sig Q
build {ℓ} Sig Q HWorld₀ = record
    { FreeK = freeK
    ; foldK = λ K → foldHom K
    ; unique = λ K h →
        let eq∂ , eqb = InitialConAlg.unique initialConAlg (conAlgOf K) (UngradedKernelHom.con-hom h)
        in (λ c →
              trans
                (UngradedKernelHom.map-encode (foldHom K) c)
                (trans
                   (cong (λ x → UngradedKernel.encode K x) (eq∂ c))
                   (sym (UngradedKernelHom.map-encode h c))))
           ,
           (λ d → eqb d)
    ; unique≃ = λ K h →
        let eq∂ , _ = InitialConAlg.unique initialConAlg (conAlgOf K) (UngradedKernelHom.con-hom h)
        in (λ γ → UngradedKernelHom.map-decode (foldHom K) γ)
           , (λ γ → UngradedKernelHom.map-decode h γ)
           , (λ γ →
                trans (UngradedKernelHom.map-decode (foldHom K) γ)
                      (trans (eq∂ (UngradedKernel.decode freeK γ))
                             (sym (UngradedKernelHom.map-decode h γ))))
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

  -- Explicit degeneracy witness: H-tier truth is vacuous (always satisfied).
  vacuousHTruth₀ : HT₀.VacuousHLayer HTruth₀
  vacuousHTruth₀ = record { satAll = λ _ _ → ttℓ }

  HInv₀ : HT₀.Invariance BB₀
  HInv₀ = record
    { Inv_H = λ c → c
    ; infl  = λ c → ConPreorder.refl (BulkBoundary.bnd BB₀)
    ; idemp-lax = λ c → ConPreorder.refl (BulkBoundary.bnd BB₀)
    }

  -- S-tier: trivial strict layer
  Fml₀ : Set ℓ
  Fml₀ = Topℓ
  module ST₀ = Truth.StrictTruth Sig
  Strict₀ : ST₀.StrictLayer Fml₀
  Strict₀ = record { Sat_S = λ _ _ → Topℓ }
  TransH₀ : Fml₀ → ConPreorder.Con (BulkBoundary.bnd BB₀)
  TransH₀ = λ _ → I∂

  -- G-tier: trivial closure and fixed point
  module GT₀ = Truth.GuardedTruth Sig Q
  GTruth₀ : GT₀.GuardedClosure (BulkBoundary.bnd BB₀)
  GTruth₀ = record
    { Flow = λ c → c
    ; mono = λ p → p
    ; infl = λ c → ConPreorder.refl (BulkBoundary.bnd BB₀)
    ; idemp-lax = λ c → ConPreorder.refl (BulkBoundary.bnd BB₀)
    ; Th* = I∂
    ; Th*-fixed = ( ConPreorder.refl (BulkBoundary.bnd BB₀) , ConPreorder.refl (BulkBoundary.bnd BB₀) )
    }

  -- Code layer as constraints
  Code₀ : Set ℓ
  Code₀ = ConPreorder.Con (BulkBoundary.bnd BB₀)
  encode₀ : ConPreorder.Con (BulkBoundary.bnd BB₀) → Code₀
  encode₀ = λ c → c
  decode₀ : Code₀ → ConPreorder.Con (BulkBoundary.bnd BB₀)
  decode₀ = λ γ → γ
  Guard₀ : Code₀ → Code₀
  Guard₀ = GT₀.GuardedClosure.Flow GTruth₀
  Body₀ : Code₀ → Code₀
  Body₀ = λ γ → γ

  freeK : UngradedKernel Sig Q
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
                (ConPreorder.refl (BulkBoundary.bnd BB₀) {c = decode₀ I∂})
              , (ConPreorder.refl (BulkBoundary.bnd BB₀) {c = decode₀ I∂})
            ; reify-decode  = λ _ → refl
            ; body-decode   = λ _ → refl
            }
        ; mono-Body∂    = λ {c} {d} le → le
        ; mono-Flow     = Truth.GuardedCore.GuardedClosure.mono GTruth₀
        ; guard-decode  = λ _ → refl
        ; decode-γ*     = refl
        }
    }

  -- Canonical fold hom into any UngradedKernel K: constraints via initialConAlg, code by encode∘map∂∘decode
  foldHom : ∀ (K : UngradedKernel Sig Q) → UngradedKernelHom freeK K
  foldHom K = record
    { con-hom   = fold≡ (conAlgOf K)
    ; mapCode   = λ γ → UngradedKernel.encode K (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (UngradedKernel.decode freeK γ))
    ; map-encode = λ c → cong (λ x → UngradedKernel.encode K (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) x)) (UngradedKernel.decode∘encode freeK c)
    ; map-decode = λ γ → UngradedKernel.decode∘encode K (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (UngradedKernel.decode freeK γ))
    }

  -- Optional promotion: Flow-preserving hom (UngradedKernelHomFlow) from FreeK to any K.
  --
  -- This is “step preservation” only: Th* transport is an additional (optional)
  -- strengthening (`UngradedKernelHomFlowStable`).
  foldFlow : ∀ (K : UngradedKernel Sig Q) → UngradedKernelHomFlow freeK K (foldHom K)
  foldFlow K = record
    { flow-hom = record
        { preserves-F  = λ c →
            GT₀.GuardedClosure.infl (UngradedKernel.GTruth K)
              (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) c)
        }
    }

  -- Stable variant: add an explicit `Th*` transport inequality.
  foldFlowStable
    : ∀ (K : UngradedKernel Sig Q)
    → (base : ConPreorder._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
                            (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (GT₀.GuardedClosure.Th* GTruth₀))
                            (Th⋆K K))
    → UngradedKernelHomFlowStable freeK K (foldHom K)
  foldFlowStable K base = record
    { stable-hom = record
        { flow-hom     = UngradedKernelHomFlow.flow-hom (foldFlow K)
        ; preserves-Th = base
        }
    }

  -- Automatic construction of the base inequality using OmegaCPO + FiniteFirst
  foldFlow-auto
    : ∀ (K : UngradedKernel Sig Q)
      (ωCPO : GT₀.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (eq-bot : ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) I∂ ≡ GT₀.OmegaCPO.⊥ ωCPO)
      → UngradedKernelHomFlowStable freeK K (foldHom K)
  foldFlow-auto K ωCPO eq-bot = foldFlowStable K base
    where
      module FB = FlowBase.For freeK
      base : ConPreorder._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
               (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) (GT₀.GuardedClosure.Th* GTruth₀))
               (GT₀.GuardedClosure.Th* (UngradedKernel.GTruth K))
      base = FB.base-from-eq-bot K (foldHom K) ωCPO eq-bot refl

  -- Variant: base via inequality map∂ I∂ ⊑ ⊥
  foldFlow-auto-ineq
    : ∀ (K : UngradedKernel Sig Q)
      (ωCPO : GT₀.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      (le-bot : ConPreorder._⊑_ (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
                              (ConAlgHom≡.map∂ (fold≡ (conAlgOf K)) I∂)
                              (GT₀.OmegaCPO.⊥ ωCPO))
      → UngradedKernelHomFlowStable freeK K (foldHom K)
  foldFlow-auto-ineq K ωCPO le-bot = foldFlowStable K base
    where
      base =
        ConPreorder.trans
          (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))
          le-bot
          (GT₀.OmegaCPO.isBot ωCPO (GT₀.GuardedClosure.Th* (UngradedKernel.GTruth K)))

-- Top-level convenience: construct a Flow-stable hom (`UngradedKernelHomFlowStable`)
-- from the initial kernel built at (Sig, Q, HWorld).

module FoldFlowBuildAuto {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  private
    module GT = Truth.GuardedTruth Sig Q

  foldFlow-build-auto
    : (HWorld : Worlds.WorldH Sig Q)
    → (K : UngradedKernel Sig Q)
    → (ωCPO : GT.OmegaCPO (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
    → (eq-bot : ConAlgHom≡.map∂ (UngradedKernelHom.con-hom (InitialKernel.foldK (build Sig Q HWorld) K)) I∂
                ≡ GT.OmegaCPO.⊥ ωCPO)
    → UngradedKernelHomFlowStable (InitialKernel.FreeK (build Sig Q HWorld)) K
        (InitialKernel.foldK (build Sig Q HWorld) K)
  foldFlow-build-auto HW K ωCPO eq-bot =
    let IK   = build Sig Q HW
        h    = InitialKernel.foldK IK K
        module FB = FlowBase.For (InitialKernel.FreeK IK)
        base = FB.base-from-eq-bot K h ωCPO eq-bot refl
    in record
      { stable-hom = record
          { flow-hom =
              record
                { preserves-F  = λ c →
                    GT.GuardedClosure.infl (UngradedKernel.GTruth K)
                      (ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h) c)
                }
          ; preserves-Th = base
          }
      }

foldFlow-build-auto = FoldFlowBuildAuto.foldFlow-build-auto
