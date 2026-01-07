{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.StablePProofSearchReflectionBarrier where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom using (KernelHom)

open import LogOS.Theorems.Meta.Base using (DeciderC; mkDeciderC; mapDeciderC)
open import LogOS.Theorems.Meta.Flow as Flow
open import LogOS.Theorems.Meta.Full as F

import LogOS.Domain.Complexity.ProofSearchBoundary as PB
import LogOS.Domain.Complexity.ResourceSchemaGraded as RSG
open import LogOS.Domain.Complexity.Poly using (PolyPred)

-- A LogOS-native Gödel-style reflection barrier:
--
-- If `P` is the kernel’s Flow stability predicate `Flow.StableP K`, then (under the
-- same FreeKernel undecidability assumption used to show `StableP` undecidable)
-- any *complete* proof system for `P` has an unbounded proof-search predicate `Prov∞`
-- that is itself undecidable.
--
-- Intuition: verification is local (decCheck), but deciding existence of *some* proof
-- is a reflection-like global predicate; in LogOS this transports to the existing
-- diagonal/Rice/Flow undecidability pipeline.

module For {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           (K : Kernel Sig Q)
           where

  module B = PB.For {ℓI = ℓ} {ℓ = ℓ} (Kernel.Code K) (Flow.StableP K)

  -- A complete proof system for stability (verification decidable; sound and complete).
  StabilityPS : Set (lsuc (lsuc ℓ))
  StabilityPS = Σ B.ProofSystem (λ PS → B.Complete PS)

  -- Transport needs the completeness witness; package it explicitly.
  Prov∞→StableP
    : ∀ {PS} → B.Complete PS → DeciderC {K = K} (B.Prov∞ PS) → DeciderC {K = K} (Flow.StableP K)
  Prov∞→StableP {PS = PS} C dec =
    mapDeciderC
      (λ γ → record
        { to   = B.Prov∞→P PS γ
        ; from = B.P→Prov∞ C γ
        })
      dec

  -- Main barrier: provability for any complete stability proof system is undecidable,
  -- because otherwise stability would be decidable, contradicting Flow’s meta theorem.
  noDecider-Prov∞-StableP
    : (HW : F.WorldH Sig Q)
      (freeNoDecider
        : ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
             (λ γ → Flow.StableP K (KernelHom.mapCode (F.foldTo Sig Q HW K) γ))))
      → ∀ (PS : B.ProofSystem) (C : B.Complete PS)
        → ¬ (DeciderC {K = K} (B.Prov∞ PS))
  noDecider-Prov∞-StableP HW freeNoDecider PS C dec =
    let noDecStable : ¬ DeciderC {K = K} (Flow.StableP K)
        noDecStable = Flow.noDecider-Stability-transport HW K freeNoDecider
    in
    noDecStable (Prov∞→StableP C dec)

  -- Resource-aware corollary:
  -- any poly-budget time/resource decider (ResourceSchemaGraded.QTimeDecider) for provability
  -- would in particular be a total decider, contradicting `noDecider-Prov∞-StableP`.
  --
  -- This is the direct bridge from the reflection barrier to a P≠NP-shaped statement
  -- (“bounded verification exists, but poly-budget proof-search does not”) for this predicate.

  noPolyBudget-Prov∞-StableP
    : ∀ (size : Kernel.Code K → ℕ) (Pℕ : PolyPred)
      (gradeBound : ℕ → QAdapter.Scale Q)
      (HW : F.WorldH Sig Q)
      (freeNoDecider
        : ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
             (λ γ → Flow.StableP K (KernelHom.mapCode (F.foldTo Sig Q HW K) γ))))
      → ∀ (PS : B.ProofSystem) (C : B.Complete PS)
        → (let module S = RSG.For {ℓI = ℓ} {ℓ = ℓ} {ℓQ = ℓ} (Kernel.Code K) size Pℕ Q gradeBound in
           ¬ (Σ (S.QTimeDecider (B.Prov∞ PS)) (λ _ → ⊤ {ℓ = lzero})))
  noPolyBudget-Prov∞-StableP size Pℕ gradeBound HW freeNoDecider PS C (qd , _) =
    let dec : DeciderC {K = K} (B.Prov∞ PS)
        dec = mkDeciderC (S.toDecider qd)
    in
    noDecider-Prov∞-StableP HW freeNoDecider PS C dec
    where
      module S = RSG.For {ℓI = ℓ} {ℓ = ℓ} {ℓQ = ℓ} (Kernel.Code K) size Pℕ Q gradeBound

  -- Grade-bound variant: any grade-bounded decider still yields a total decider.
  noTimeBoundedG-Prov∞-StableP
    : ∀ (size : Kernel.Code K → ℕ) (Pℕ : PolyPred)
      (gradeBound : ℕ → QAdapter.Scale Q)
      (HW : F.WorldH Sig Q)
      (freeNoDecider
        : ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
             (λ γ → Flow.StableP K (KernelHom.mapCode (F.foldTo Sig Q HW K) γ))))
      → ∀ (PS : B.ProofSystem) (C : B.Complete PS)
        → (let module S = RSG.For {ℓI = ℓ} {ℓ = ℓ} {ℓQ = ℓ} (Kernel.Code K) size Pℕ Q gradeBound in
           ¬ (Σ (S.QTimeDeciderG (B.Prov∞ PS)) (λ _ → ⊤ {ℓ = lzero})))
  noTimeBoundedG-Prov∞-StableP size Pℕ gradeBound HW freeNoDecider PS C (qd , _) =
    let dec : DeciderC {K = K} (B.Prov∞ PS)
        dec = mkDeciderC (S.toDeciderG qd)
    in
    noDecider-Prov∞-StableP HW freeNoDecider PS C dec
    where
      module S = RSG.For {ℓI = ℓ} {ℓ = ℓ} {ℓQ = ℓ} (Kernel.Code K) size Pℕ Q gradeBound
