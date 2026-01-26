{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
open import LogOS.Prelude.Product using (fst)
open import LogOS.API.Assumptions.Core using (LogicCore; coreFromKernel)
open import LogOS.Domain.ZFC.SetTheory.Pack as ZFC
open import LogOS.Theorems.Meta.Assumptions.Diagonal as Diag
open import LogOS.Theorems.Meta.GRHBridge as GRHB

open import LogOS.Domain.Opacity.TruthSeparation as TruthSep

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- ZFC-driven stability pack: relate ZFC axioms + diagonal witnesses to the
-- Flow projector on the boundary to obtain a canonical nucleus bridge.

record FlowStability {ℓ}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K   : Kernel Sig Q)
                     (RS  : RiemannSpectral)
                     : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  open RiemannSpectral RS using (Spectral; NontrivialZero; OnLine)

  core : LogicCore {ℓ}
  core = coreFromKernel K

  field
    c : Spectral → ConPreorder.Con (BulkBoundary.bnd BB)

    -- Nontrivial zeros land in the Flow-closed fragment (one inequality).
    -- The other inequality is always available from `infl` for the Flow closure operator.
    zero→Flow-closed
      : ∀ s → NontrivialZero s →
        ConPreorder._⊑_ (BulkBoundary.bnd BB) (Endo.fn (Flow-Endo K) (c s)) (c s)

    Flow-stable→OnLine
      : ∀ s →
        (ConPreorder._⊑_ (BulkBoundary.bnd BB) (Endo.fn (Flow-Endo K) (c s)) (c s)
       × ConPreorder._⊑_ (BulkBoundary.bnd BB) (c s) (Endo.fn (Flow-Endo K) (c s)))
        → OnLine s

  zero→Flow-stable
    : ∀ s → NontrivialZero s →
      ConPreorder._⊑_ (BulkBoundary.bnd BB) (Endo.fn (Flow-Endo K) (c s)) (c s)
      × ConPreorder._⊑_ (BulkBoundary.bnd BB) (c s) (Endo.fn (Flow-Endo K) (c s))
  zero→Flow-stable s nz = zero→Flow-closed s nz , infl (TruthSep.FlowClosureOp K) (c s)

-- Bundle ZFC + diagonalisation separately (ledger fields), while keeping the
-- GRH-relevant stability data minimal.

record ZFCFlowStability {ℓ}
                        {Sig : LogOSSignature ℓ}
                        {Q   : QAdapter ℓ}
                        (K   : Kernel Sig Q)
                        (RS  : RiemannSpectral)
                        : Set (lsuc (lsuc ℓ)) where
  coreLK : LogicCore {ℓ}
  coreLK = coreFromKernel K

  field
    zf   : ZFC.ZFAxioms (kernelLike-fromKernel K)
    diag : Diag.Diagonal K
    core : FlowStability {ℓ} {Sig} {Q} K RS

  open FlowStability core public using (c; zero→Flow-stable; zero→Flow-closed; Flow-stable→OnLine)

-- Equality-to-pair helper: turn Flow-fixed equalities into the pair of
-- inequalities needed by the nucleus bridge.

Flow-eq→stable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    {c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))}
  → Endo.fn (Flow-Endo K) c ≡ c
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Endo.fn (Flow-Endo K) c) c
  × ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c (Endo.fn (Flow-Endo K) c)
Flow-eq→stable {K = K} {c} eq =
  let open Kernel K
      CP = BulkBoundary.bnd BB
      reflC = ConPreorder.refl CP {c = c}
      le₁ = subst (λ x → ConPreorder._⊑_ CP x c) (sym eq) reflC
      le₂ = subst (λ x → ConPreorder._⊑_ CP c x) (sym eq) reflC
  in le₁ , le₂

-- Build the canonical Flow nucleus bridge from the ZFC stability pack.

flowTruthSeparation
  : ∀ {ℓ Sig Q} {K : Kernel Sig Q}
    (RS   : RiemannSpectral)
    (Stab : FlowStability {ℓ} {Sig} {Q} K RS)
  → TruthSep.FlowTruthSeparation K RS
flowTruthSeparation {K = K} RS Stab =
  record
    { c = FlowStability.c Stab
    ; zero-ref =
        record
          { sat-→ = λ _ s nz → FlowStability.zero→Flow-closed Stab s nz
          }
    ; JClosed-ref =
        record
          { sat-→ =
              λ _ s closed →
                FlowStability.Flow-stable→OnLine Stab s
                  (closed , infl (TruthSep.FlowClosureOp K) (FlowStability.c Stab s))
          }
    }

flowBridge
  : ∀ {ℓ Sig Q} {K : Kernel Sig Q}
    (RS   : RiemannSpectral)
    (Stab : FlowStability {ℓ} {Sig} {Q} K RS)
  → GRHB.GlobalNucleusBridge K (TruthSep.RStoSP RS)
flowBridge {K = K} RS Stab =
  TruthSep.flowNucleusBridge K RS (flowTruthSeparation RS Stab)

-- GRH via the canonical nucleus interpretation of ZFC stability.

GRH_Without_Vacuity_Guards_from_FlowStability
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K    : Kernel Sig Q)
    (RS   : RiemannSpectral)
    (Stab : FlowStability {ℓ} {Sig} {Q} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_FlowStability K RS Stab =
  TruthSep.GRH_Without_Vacuity_Guards_from_FlowTruthSeparation K RS (flowTruthSeparation RS Stab)

GRH_Without_Vacuity_Guards_from_ZFCStability
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K    : Kernel Sig Q)
    (RS   : RiemannSpectral)
    (Stab : ZFCFlowStability {ℓ} {Sig} {Q} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_ZFCStability K RS Stab =
  GRH_Without_Vacuity_Guards_from_FlowStability K RS (ZFCFlowStability.core Stab)
