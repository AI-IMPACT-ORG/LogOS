{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.ZFCBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Domain.SetTheory.Pack as ZFC
open import LogOS.Theorems.Meta.Diagonal as Diag
open import LogOS.Theorems.Meta.GRHBridge as GRHB

open import LogOS.Domain.Opacity.TruthSeparation as TruthSep

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- ZFC-driven stability pack: relate ZFC axioms + diagonal witnesses to the
-- Flow projector on the boundary to obtain a canonical nucleus bridge.

record ZFCFlowStability {ℓ}
                        {Sig : LogOSSignature ℓ}
                        {Q   : QAdapter ℓ}
                        (K   : Kernel Sig Q)
                        (RS  : RiemannSpectral)
                        : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  open RiemannSpectral RS
  field
    zf   : ZFC.ZFAxioms K
    diag : Diag.Diagonal K

    c : Spectral → ConPoset.Con (BulkBoundary.bnd BB)

    zero→Flow-stable
      : ∀ s → NontrivialZero s →
        ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn (Flow-Endo K) (c s)) (c s)
        × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Endo.fn (Flow-Endo K) (c s))

    Flow-stable→OnLine
      : ∀ s →
        (ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn (Flow-Endo K) (c s)) (c s)
       × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Endo.fn (Flow-Endo K) (c s)))
        → OnLine s

-- Equality-to-pair helper: turn Flow-fixed equalities into the pair of
-- inequalities needed by the nucleus bridge.

Flow-eq→stable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    {c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))}
  → Endo.fn (Flow-Endo K) c ≡ c
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Endo.fn (Flow-Endo K) c) c
  × ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c (Endo.fn (Flow-Endo K) c)
Flow-eq→stable {K = K} {c} eq =
  let open Kernel K
      CP = BulkBoundary.bnd BB
      reflC = ConPoset.refl CP {c = c}
      le₁ = subst (λ x → ConPoset._⊑_ CP x c) (sym eq) reflC
      le₂ = subst (λ x → ConPoset._⊑_ CP c x) (sym eq) reflC
  in le₁ , le₂

-- Build the canonical Flow nucleus bridge from the ZFC stability pack.

flowBridge
  : ∀ {ℓ Sig Q} {K : Kernel Sig Q}
    (RS   : RiemannSpectral)
    (Stab : ZFCFlowStability {ℓ} {Sig} {Q} K RS)
  → GRHB.GlobalNucleusBridge K (TruthSep.RStoSP RS)
flowBridge {K = K} RS Stab = record
  { Pr = GRHB.FlowProjector K
  ; c  = ZFCFlowStability.c Stab
  ; zero→PFixed = ZFCFlowStability.zero→Flow-stable Stab
  ; PFixed→OnLine = ZFCFlowStability.Flow-stable→OnLine Stab
  }

-- GRH via the canonical nucleus interpretation of ZFC stability.

GRH_Without_Vacuity_Guards_from_ZFCStability
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K    : Kernel Sig Q)
    (RS   : RiemannSpectral)
    (Stab : ZFCFlowStability {ℓ} {Sig} {Q} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_ZFCStability K RS Stab =
  GRHB.GRH_Without_Vacuity_Guards_via_GlobalNucleus K (TruthSep.RStoSP RS) (flowBridge RS Stab)
