{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Arguments.ScalingLaws where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.Graded.ToKernel as ToKernel
open import LogOS.Kernel as Kernel

import LogOS.Packs.Agents.Learning.RGFlow as RGFlow
import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.LimitPublicisation as LP

-- Tight, reflection-closed scaling-law surface for RG learning steps.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RG = RGFlow.For K ωCPO
  open RG using (Policy; RGStep; RGStable; ScalingDimension; rg-iter; rg-μ; rg-least-stable; scaling-iter)

  open QAdapter Q using (_≤s_)
  open GradedKernel K using (Code; decode; reify)

  -- Observables at the least RG-stable policy are minimal among stable points.
  obs-μ≤stable
    : ∀ {g} (s : RGStep g) (D : ScalingDimension s) {c : Policy}
    → RGStable s c
    → _≤s_ (ScalingDimension.obs D (rg-μ s))
           (ScalingDimension.obs D c)
  obs-μ≤stable s D st =
    ScalingDimension.mono D (rg-least-stable s st)

  -- Scaling-law witness for a code-level policy, pinned to rg-μ.
  ScalingBound
    : ∀ {g} (s : RGStep g) (D : ScalingDimension s)
    → Code → Set ℓ
  ScalingBound s D γ =
    _≤s_ (ScalingDimension.obs D (rg-μ s))
         (ScalingDimension.obs D (decode γ))

  -- Alias for the core scaling-law iterate bound.
  scaling-law
    : ∀ {g} {s : RGStep g} (D : ScalingDimension s)
    → ∀ n
    → _≤s_ (ScalingDimension.obs D (rg-iter s n))
           (QAdapter._·_ Q
             (RG.scalePow n (RG.ScaleAction.act (ScalingDimension.action D) g))
             (ScalingDimension.obs D (rg-iter s zero)))
  scaling-law = scaling-iter

  scalingBound-from-stable
    : ∀ {g} (s : RGStep g) (D : ScalingDimension s) {γ}
    → RGStable s (decode γ)
    → ScalingBound s D γ
  scalingBound-from-stable s D st = obs-μ≤stable s D st

  scalingBound-ext
    : ∀ {g} {s : RGStep g} {D : ScalingDimension s} γ δ
    → decode γ ≡ decode δ
    → ScalingBound s D γ
    → ScalingBound s D δ
  scalingBound-ext {s = s} {D = D} γ δ eq bound =
    subst
      (λ c → _≤s_ (ScalingDimension.obs D (rg-μ s))
                  (ScalingDimension.obs D c))
      eq
      bound

  -- Reflection closure: reify is observationally inert for ScalingBound.
  scalingBound-reify
    : ∀ {g} {s : RGStep g} {D : ScalingDimension s} γ
    → ScalingBound s D (reify γ) ↔ ScalingBound s D γ
  scalingBound-reify {s = s} {D = D} γ =
    let eq = GradedKernel.reify-decode K γ in
    record
      { to   = λ bound → scalingBound-ext {s = s} {D = D} (reify γ) γ eq bound
      ; from = λ bound → scalingBound-ext {s = s} {D = D} γ (reify γ) (sym eq) bound
      }

  -- Optional: when step-grade = sat, publicise ScalingBound via Pr.
  module Public
    {stepSat : ToKernel.StepIsSat K}
    where

    K₀ : Kernel Sig Q
    K₀ = ToKernel.asKernel K stepSat

    ScalingBoundK
      : ∀ {g} (s : RGStep g) (D : ScalingDimension s)
      → Kernel.Code K₀ → Set ℓ
    ScalingBoundK s D γ = ScalingBound s D γ

    scalingBound-extK
      : ∀ {g} {s : RGStep g} {D : ScalingDimension s}
      → Comm.DecodeExtensional′ K₀ (ScalingBoundK s D)
    scalingBound-extK {s = s} {D = D} γ₁ γ₂ eq bound =
      scalingBound-ext {s = s} {D = D} γ₁ γ₂ eq bound

    scalingBound-public
      : ∀ {g} (s : RGStep g) (D : ScalingDimension s)
      → (stable : ∀ γ →
          ScalingBoundK s D γ ↔ ScalingBoundK s D (Kernel.FlowCode K₀ γ))
      → ∀ {γ} → ScalingBoundK s D γ
      → LP.LimitPublicisation K₀ (ScalingBoundK s D) γ
    scalingBound-public s D stable bound =
      LP.TruthK→Pr K₀ (ScalingBoundK s D) (scalingBound-extK {s = s} {D = D}) stable bound

    scalingBound-public-reify
      : ∀ {ℓC} {g} (s : RGStep g) (D : ScalingDimension s)
      → ∀ {γ}
      → LP.LimitPublicisation {ℓC = ℓC} K₀ (ScalingBoundK s D) γ
      ↔ LP.LimitPublicisation {ℓC = ℓC} K₀ (ScalingBoundK s D) (Kernel.reify K₀ γ)
    scalingBound-public-reify {ℓC = ℓC} s D {γ} =
      LP.Pr-naturality {ℓC = ℓC} K₀ (ScalingBoundK s D) (Kernel.reify K₀)
        (Kernel.reify-decode K₀)
