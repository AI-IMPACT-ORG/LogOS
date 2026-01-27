{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.QuickWins where

-- Small, assumption-light wrappers around existing graded boundary theorems.
-- Goal: make the standard μ/endomap/S↔H moves available as one-liners.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Endo
open import LogOS.Kernel.Graded.Hom
import LogOS.Kernel.Graded.Reachability as KR
open import LogOS.Theorems.Boundary.Graded.Mu
open import LogOS.Theorems.Code.Graded as Code

-- μ-style induction (boundary): prefixed points bound Th⋆ (lightweight wrapper over μ-induction-K).

prefixed→Th⋆≤
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
    (c    : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K)) c)
                 c
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Th* (GradedKernel.GTruth K))
                 c
prefixed→Th⋆≤ Sig Q K ωCPO FF c = μ-induction-K Sig Q K ωCPO FF c

-- Textbook aliases.
-- Park induction / least prefixed point principle (at saturation grade):
-- if Flow sat c ⊑ c then Th⋆ ⊑ c.

park-induction = prefixed→Th⋆≤
least-prefixed-point = prefixed→Th⋆≤

-- Transport of the guarded fixed point through endomap bounds.

Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Th⋆≤fTh⋆ = Flow≤f→Th⋆≤fTh⋆

fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
fTh⋆≤Th⋆ = f≤Flow→fTh⋆≤Th⋆

-- Boundary-side monotonicity helpers (H-tier + S-transport).

Sat_H-mono-Con
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    {w : LogOSSignature.Cosp Sig}
    {c c' : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))}
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) c c'
  → Truth.HomotypicalTruth.HLayer.Sat_H (GradedKernel.HTruth K) w c
  → Truth.HomotypicalTruth.HLayer.Sat_H (GradedKernel.HTruth K) w c'
Sat_H-mono-Con Sig Q K = Truth.HomotypicalTruth.HLayer.mono-Con (GradedKernel.HTruth K)

Sat_H-mono-ctx
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    {w w' : LogOSSignature.Cosp Sig}
    {c : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))}
  → Worlds.WorldH._≤ctx_ (GradedKernel.HWorld K) w w'
  → Truth.HomotypicalTruth.HLayer.Sat_H (GradedKernel.HTruth K) w c
  → Truth.HomotypicalTruth.HLayer.Sat_H (GradedKernel.HTruth K) w' c
Sat_H-mono-ctx Sig Q K = Truth.HomotypicalTruth.HLayer.mono-ctx (GradedKernel.HTruth K)

-- Boundary-facing satisfaction is monotone in constraints, transported from Sat_H
-- via the kernel coherence `sat-coh`.

Sat_H_bnd-mono-Con
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (w : LogOSSignature.Cosp Sig)
    {c c' : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))}
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) c c'
  → GradedKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
  → GradedKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c'
Sat_H_bnd-mono-Con Sig Q K w le sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (GradedKernel.HWorld K)
    coh₁ = GradedKernel.sat-coh K w _
    coh₂ = GradedKernel.sat-coh K w _
    satH  : HT.HLayer.Sat_H (GradedKernel.HTruth K) w _
    satH  = Prop._↔_.from coh₁ sat
    satH' : HT.HLayer.Sat_H (GradedKernel.HTruth K) w _
    satH' = HT.HLayer.mono-Con (GradedKernel.HTruth K) le satH
  in Prop._↔_.to coh₂ satH'

-- Textbook alias: inherited monotonicity on the coherent boundary fragment (p = bnd w).

boundary-sat-mono-Con = Sat_H_bnd-mono-Con

Sat_H_bnd-mono-ctx
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    {w w' : LogOSSignature.Cosp Sig}
    {c : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))}
  → Worlds.WorldH._≤ctx_ (GradedKernel.HWorld K) w w'
  → GradedKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
  → GradedKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w') c
Sat_H_bnd-mono-ctx Sig Q K le sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (GradedKernel.HWorld K)
    coh₁ = GradedKernel.sat-coh K _ _
    coh₂ = GradedKernel.sat-coh K _ _
    satH  : HT.HLayer.Sat_H (GradedKernel.HTruth K) _ _
    satH  = Prop._↔_.from coh₁ sat
    satH' : HT.HLayer.Sat_H (GradedKernel.HTruth K) _ _
    satH' = HT.HLayer.mono-ctx (GradedKernel.HTruth K) le satH
  in Prop._↔_.to coh₂ satH'

boundary-sat-mono-ctx = Sat_H_bnd-mono-ctx

Sat_H-inv
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    {w : LogOSSignature.Cosp Sig}
    {c : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))}
  → Truth.HomotypicalTruth.HLayer.Sat_H (GradedKernel.HTruth K) w c
  → Truth.HomotypicalTruth.HLayer.Sat_H (GradedKernel.HTruth K) w
      (Truth.HomotypicalTruth.Invariance.Inv_H (GradedKernel.HInv K) c)
Sat_H-inv Sig Q K sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (GradedKernel.HWorld K)
    inv = GradedKernel.HInv K
    le  = HT.Invariance.infl inv _
  in HT.HLayer.mono-Con (GradedKernel.HTruth K) le sat

-- ============================================================================
-- Step vs saturation: iterated step flow is always bounded by saturation.
-- ============================================================================

iterStep
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ℕ
  → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))
  → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))
iterStep K zero    c = c
iterStep K (suc n) c =
  GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K) (iterStep K n c)

-- Textbook alias: n-step iteration of the one-step flow.

step-iteration = iterStep

iterStep≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ∀ n c
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (iterStep K n c)
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K)) c)
iterStep≤sat K zero c =
  GradedClosure.infl-sat (GradedKernel.GTruth K) c
iterStep≤sat K (suc n) c =
  let
    open GradedKernel K
    CP = BulkBoundary.bnd BB
    trans⊑ = ConPreorder.trans CP
    ih = iterStep≤sat K n c
    step-mono = GradedClosure.mono GTruth {g = step-grade} ih
    step≤sat' = GradedClosure.mono-grade GTruth (step≤sat K)
                  (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) c)
    sat-idemp = GradedClosure.idemp-sat GTruth c
  in trans⊑ step-mono (trans⊑ step≤sat' sat-idemp)

-- Textbook alias: any finite number of step iterations is bounded by saturation.

step-iteration≤sat = iterStep≤sat

-- Saturation absorption (graded): saturating after any grade cannot overshoot
-- saturating directly.

sat-absorb
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ∀ g c
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedClosure.Flow (GradedKernel.GTruth K) g c))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K)) c)
sat-absorb {Q = Q} K g c =
  let
    open GradedKernel K
    module Q0 = QAdapter Q
    CP = BulkBoundary.bnd BB
    trans⊑ = ConPreorder.trans CP
    G = GTruth
    sat = GradedClosure.sat G
    step₁ = GradedClosure.comp-lax G g sat c
    step₂ = GradedClosure.mono-grade G (GradedClosure.sat-top G (Q0._·_ g sat)) c
  in trans⊑ step₁ step₂

-- Textbook alias: closure absorption.

saturation-absorption = sat-absorb

-- Optional: link (n+1) step iterations to grade multiplication via `comp-lax`.
-- This is useful as a direction-check for the grade order convention.

powStep
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ℕ → QAdapter.Scale Q
powStep {Q = Q} K zero    = GradedKernel.step-grade K
powStep {Q = Q} K (suc n) = QAdapter._·_ Q (powStep K n) (GradedKernel.step-grade K)

iterStepPow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ∀ n c
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (iterStep K (suc n) c)
      (GradedClosure.Flow (GradedKernel.GTruth K) (powStep K n) c)
iterStepPow K zero c =
  let
    open GradedKernel K
    CP = BulkBoundary.bnd BB
  in ConPreorder.refl CP
iterStepPow K (suc n) c =
  let
    open GradedKernel K
    CP = BulkBoundary.bnd BB
    trans⊑ = ConPreorder.trans CP
    ih = iterStepPow K n c
    step-mono = GradedClosure.mono GTruth {g = step-grade} ih
    step-comp = GradedClosure.comp-lax GTruth (powStep K n) step-grade c
  in trans⊑ step-mono step-comp

-- Textbook alias: graded step power law (stepⁿ bounded by grade-power).

step-power-law = iterStepPow

-- ============================================================================
-- Reachability view (Q-graded): `c ⟶[g] d` iff `d ⊑ Flow g c`.
-- ============================================================================

module ReachabilityView where
  module For
    {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    where

    module R = KR.For K
    open R public using (_⟶[_]_; _⟶⋆_)

    -- Any finite number of step-iterations is reachable at saturation grade.
    iterStep⟶⋆
      : ∀ n c → c ⟶⋆ iterStep K n c
    iterStep⟶⋆ n c = iterStep≤sat K n c

    -- (n+1)-step iteration is reachable at the “power grade” `powStep`.
    iterStep⟶pow
      : ∀ n c → c ⟶[ powStep K n ] iterStep K (suc n) c
    iterStep⟶pow n c = iterStepPow K n c

ineq→Sat_S
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (φ ψ : GradedKernel.Fml K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (GradedKernel.TransH K φ) (GradedKernel.TransH K ψ)
  → ∀ (w : LogOSSignature.Cosp Sig)
    → Truth.StrictTruth.StrictLayer.Sat_S (GradedKernel.Strict K) w φ
    → Truth.StrictTruth.StrictLayer.Sat_S (GradedKernel.Strict K) w ψ
ineq→Sat_S Sig Q K φ ψ le w p =
  let
    module HT = Truth.HomotypicalTruth Sig Q (GradedKernel.HWorld K)
    cL = GradedKernel.coh-LH K w φ
    cR = GradedKernel.coh-LH K w ψ
    pH : HT.HLayer.Sat_H (GradedKernel.HTruth K) w (GradedKernel.TransH K φ)
    pH = Prop._↔_.to cL p
    qH : HT.HLayer.Sat_H (GradedKernel.HTruth K) w (GradedKernel.TransH K ψ)
    qH = HT.HLayer.mono-Con (GradedKernel.HTruth K) le pH
  in Prop._↔_.from cR qH

-- Guarded code naturality (decode-level) as a ready-to-use corollary.

guard-naturality
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    (h : GradedKernelHom K₁ K₂)
    (presFlow : GradedKernelHomFlow K₁ K₂ h)
    (γ : GradedKernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                 (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Guard K₁ γ)))
                 (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
                   (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
guard-naturality h presFlow γ = Code.guard-naturality-decode _ _ h presFlow γ
