{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.ZFCBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Closure using (infl)
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import Data.Product using (fst)
open import LogOS.Domain.ZFC.SetTheory.Pack as ZFC
open import LogOS.Theorems.Meta.Assumptions.Diagonal as Diag
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

flowTruthSeparation
  : ∀ {ℓ Sig Q} {K : Kernel Sig Q}
    (RS   : RiemannSpectral)
    (Stab : ZFCFlowStability {ℓ} {Sig} {Q} K RS)
  → TruthSep.FlowTruthSeparation K RS
flowTruthSeparation {K = K} RS Stab =
  record
    { c = ZFCFlowStability.c Stab
    ; zero→JClosed = λ s nz → fst (ZFCFlowStability.zero→Flow-stable Stab s nz)
    ; JClosed→OnLine =
        λ s closed →
          ZFCFlowStability.Flow-stable→OnLine Stab s
            (closed , infl (TruthSep.FlowClosureOp K) (ZFCFlowStability.c Stab s))
    }

flowBridge
  : ∀ {ℓ Sig Q} {K : Kernel Sig Q}
    (RS   : RiemannSpectral)
    (Stab : ZFCFlowStability {ℓ} {Sig} {Q} K RS)
  → GRHB.GlobalNucleusBridge K (TruthSep.RStoSP RS)
flowBridge {K = K} RS Stab =
  TruthSep.flowNucleusBridge K RS (flowTruthSeparation RS Stab)

-- GRH via the canonical nucleus interpretation of ZFC stability.

GRH_Without_Vacuity_Guards_from_ZFCStability
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K    : Kernel Sig Q)
    (RS   : RiemannSpectral)
    (Stab : ZFCFlowStability {ℓ} {Sig} {Q} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_ZFCStability K RS Stab =
  TruthSep.GRH_Without_Vacuity_Guards_from_FlowTruthSeparation K RS (flowTruthSeparation RS Stab)
