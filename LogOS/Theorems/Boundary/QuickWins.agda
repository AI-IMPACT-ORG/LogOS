{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.QuickWins where

-- Small, assumption-light wrappers around existing boundary theorems.
-- Goal: make the standard μ/endomap/S↔H moves available as one-liners.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Kernel.Hom
open import LogOS.Theorems.Boundary.Mu
open import LogOS.Theorems.SemanticCut as Cut
open import LogOS.Theorems.Code.Core as Code
open import LogOS.Syntax.Prop as Prop

-- μ-style induction (boundary): prefixed points bound Th⋆ (lightweight wrapper over μ-induction-K).

prefixed→Th⋆≤
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
    (c    : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K)))
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Endo.fn (Flow-Endo K) c)
                 c
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Th⋆K K)
                 c
prefixed→Th⋆≤ Sig Q K ωCPO FF c = μ-induction-K Sig Q K ωCPO FF c

-- Textbook aliases.
-- Park induction / least prefixed point principle: if Flow c ⊑ c then Th⋆ ⊑ c.

park-induction = prefixed→Th⋆≤
least-prefixed-point = prefixed→Th⋆≤

-- Transport of the guarded fixed point through endomap bounds (re-exposes the DSL helpers).

Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Th⋆≤fTh⋆ = Flow≤f→Th⋆≤fTh⋆

fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
fTh⋆≤Th⋆ = f≤Flow→fTh⋆≤Th⋆

-- Boundary-side monotonicity helpers (H-tier + S-transport).

Sat_H-mono-Con
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    {w : LogOSSignature.Cosp Sig}
    {c c' : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))}
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c c'
  → Truth.HomotypicalTruth.HLayer.Sat_H (Kernel.HTruth K) w c
  → Truth.HomotypicalTruth.HLayer.Sat_H (Kernel.HTruth K) w c'
Sat_H-mono-Con Sig Q K = Truth.HomotypicalTruth.HLayer.mono-Con (Kernel.HTruth K)

Sat_H-mono-ctx
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    {w w' : LogOSSignature.Cosp Sig}
    {c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))}
  → Worlds.WorldH._≤ctx_ (Kernel.HWorld K) w w'
  → Truth.HomotypicalTruth.HLayer.Sat_H (Kernel.HTruth K) w c
  → Truth.HomotypicalTruth.HLayer.Sat_H (Kernel.HTruth K) w' c
Sat_H-mono-ctx Sig Q K = Truth.HomotypicalTruth.HLayer.mono-ctx (Kernel.HTruth K)

-- Boundary-facing satisfaction is monotone in constraints, transported from Sat_H
-- via the kernel coherence `sat-coh`.

Sat_H_bnd-mono-Con
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (w : LogOSSignature.Cosp Sig)
    {c c' : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))}
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c c'
  → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
  → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c'
Sat_H_bnd-mono-Con Sig Q K w le sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    coh₁ = Kernel.sat-coh K w _
    coh₂ = Kernel.sat-coh K w _
    satH  : HT.HLayer.Sat_H (Kernel.HTruth K) w _
    satH  = Prop._↔_.from coh₁ sat
    satH' : HT.HLayer.Sat_H (Kernel.HTruth K) w _
    satH' = HT.HLayer.mono-Con (Kernel.HTruth K) le satH
  in Prop._↔_.to coh₂ satH'

-- Textbook alias: inherited monotonicity on the coherent boundary fragment (p = bnd w).

boundary-sat-mono-Con = Sat_H_bnd-mono-Con

-- Boundary-facing satisfaction is monotone in worlds (via Sat_H mono-ctx and sat-coh).

Sat_H_bnd-mono-ctx
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    {w w' : LogOSSignature.Cosp Sig}
    {c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))}
  → Worlds.WorldH._≤ctx_ (Kernel.HWorld K) w w'
  → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
  → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w') c
Sat_H_bnd-mono-ctx Sig Q K le sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    coh₁ = Kernel.sat-coh K _ _
    coh₂ = Kernel.sat-coh K _ _
    satH  : HT.HLayer.Sat_H (Kernel.HTruth K) _ _
    satH  = Prop._↔_.from coh₁ sat
    satH' : HT.HLayer.Sat_H (Kernel.HTruth K) _ _
    satH' = HT.HLayer.mono-ctx (Kernel.HTruth K) le satH
  in Prop._↔_.to coh₂ satH'

boundary-sat-mono-ctx = Sat_H_bnd-mono-ctx

-- Invariance closure is sound for satisfaction: Sat_H w c → Sat_H w (Inv_H c).

Sat_H-inv
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    {w : LogOSSignature.Cosp Sig}
    {c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))}
  → Truth.HomotypicalTruth.HLayer.Sat_H (Kernel.HTruth K) w c
  → Truth.HomotypicalTruth.HLayer.Sat_H (Kernel.HTruth K) w
      (Truth.HomotypicalTruth.Invariance.Inv_H (Kernel.HInv K) c)
Sat_H-inv Sig Q K sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    inv = Kernel.HInv K
    le  = HT.Invariance.infl inv _
  in HT.HLayer.mono-Con (Kernel.HTruth K) le sat

ineq→Sat_S
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (φ ψ : Kernel.Fml K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Kernel.TransH K φ) (Kernel.TransH K ψ)
  → Cut.Ent_S Sig Q K φ ψ
ineq→Sat_S = Cut.ineq→Ent_S

-- Guarded code naturality (decode-level) as a ready-to-use corollary.

guard-naturality
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    (presFlow : KernelHomFlow K₁ K₂ h)
    (γ : Kernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
                 (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Guard K₁ γ)))
                 (Endo.fn (Flow-Endo K₂) (Kernel.decode K₂ (KernelHom.mapCode h γ)))
guard-naturality h presFlow γ = Code.guard-naturality-decode _ _ h presFlow γ
