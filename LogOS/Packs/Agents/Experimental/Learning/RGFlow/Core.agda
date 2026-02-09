{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Learning.RGFlow.Core where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Prelude using (ℕ; zero; suc)

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded.Endo as GEndo
open import LogOS.Kernel.Graded.ConAlgOf using (conAlgOf)
open import LogOS.Minimal.ConAlg using (ConAlg)
import LogOS.Packs.Agents.EndoFixedPoint as EndoFP

-- Experimental: RG-flow stability for learning (depends on complexity/physics
-- assumptions). Uses graded closure steps as coarse-graining maps with μ-fixed
-- points and prequantale-grade composition.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  open QAdapter Q using (Time; τ)

  open LogOSSignature Sig using (Cosp)

  open GradedKernel K using (BB)
  open BulkBoundary BB using (Con_bnd)
  open GEndo

  module FP = EndoFP.Graded.For K ωCPO
  open FP using (_⊑_; iterEndo; muEndo; muEndo-unfold-left; muEndo-induction;
                 ScottContinuous; iterEndo-mono-chain-infl; muEndo-unfold-right-infl)
  module μ = FP

  Policy : Set ℓ
  Policy = Con_bnd

  conAlg : ConAlg {ℓ}
  conAlg = conAlgOf K

  open ConAlg conAlg using (_⊗∂_; I∂)

  RGStep : QAdapter.Scale Q → Set (lsuc ℓ)
  RGStep g = ClosureStepAt K g

  applyRG : ∀ {g} → RGStep g → Policy → Policy
  applyRG s = Endo.fn (ClosureStepAt.endo s)

  rg-iter : ∀ {g} → RGStep g → ℕ → Policy
  rg-iter s = iterEndo (ClosureStepAt.endo s)

  rg-μ : ∀ {g} → RGStep g → Policy
  rg-μ s = muEndo (ClosureStepAt.endo s)

  -- Prequantale-indexed composition (hidden categorical structure).
  rg-compose : ∀ {g₁ g₂} → RGStep g₁ → RGStep g₂ → RGStep (QAdapter._·_ Q g₁ g₂)
  rg-compose = _thenStepAt_

  rg-promote : ∀ {g g'} → QAdapter._≤s_ Q g g' → RGStep g → RGStep g'
  rg-promote = promoteStep

  -- Fixed-point facts (RG stability via μ).
  rg-unfold-left
    : ∀ {g} (s : RGStep g)
    → _⊑_ (rg-μ s) (applyRG s (rg-μ s))
  rg-unfold-left s =
    muEndo-unfold-left (ClosureStepAt.endo s)

  rg-induction
    : ∀ {g} (s : RGStep g) (c : Policy)
    → _⊑_ (applyRG s c) c
    → _⊑_ (rg-μ s) c
  rg-induction s c pre =
    muEndo-induction (ClosureStepAt.endo s) c pre

  rg-chain
    : ∀ {g} (s : RGStep g)
    → ∀ n → _⊑_ (rg-iter s n) (rg-iter s (suc n))
  rg-chain s =
    iterEndo-mono-chain-infl (ClosureStepAt.endo s) (ClosureStepAt.infl s)

  rg-unfold-right
    : ∀ {g} (s : RGStep g)
    → ScottContinuous (Endo.fn (ClosureStepAt.endo s))
    → _⊑_ (applyRG s (rg-μ s)) (rg-μ s)
  rg-unfold-right s SC =
    muEndo-unfold-right-infl (ClosureStepAt.endo s) SC (ClosureStepAt.infl s)

  record RGStable {g : QAdapter.Scale Q} (s : RGStep g) (c : Policy) : Set ℓ where
    field
      closed : _⊑_ (applyRG s c) c

  rg-least-stable
    : ∀ {g} (s : RGStep g) {c : Policy}
    → RGStable s c
    → _⊑_ (rg-μ s) c
  rg-least-stable s st = rg-induction s _ (RGStable.closed st)

  -- Lyapunov-style stability with prequantale-valued potentials.
  record RGPotential : Set (lsuc (lsuc ℓ)) where
    field
      Φ : Policy → QAdapter.Scale Q
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (Φ c) (Φ d)

  record RGLyapunov {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      potential : RGPotential
      decrease : ∀ c → QAdapter._≤s_ Q
                   (RGPotential.Φ potential (applyRG s c))
                   (RGPotential.Φ potential c)

  rg-lyapunov-step
    : ∀ {g} (s : RGStep g) (L : RGLyapunov s) (c : Policy)
    → QAdapter._≤s_ Q
        (RGPotential.Φ (RGLyapunov.potential L) (applyRG s c))
        (RGPotential.Φ (RGLyapunov.potential L) c)
  rg-lyapunov-step s L c = RGLyapunov.decrease L c

  rg-lyapunov-iter
    : ∀ {g} (s : RGStep g) (L : RGLyapunov s)
    → ∀ n → QAdapter._≤s_ Q
        (RGPotential.Φ (RGLyapunov.potential L) (rg-iter s (suc n)))
        (RGPotential.Φ (RGLyapunov.potential L) (rg-iter s n))
  rg-lyapunov-iter s L zero =
    rg-lyapunov-step s L (rg-iter s zero)
  rg-lyapunov-iter s L (suc n) =
    rg-lyapunov-step s L (rg-iter s (suc n))

  -- -----------------------------------------------------------------------
  -- CFT-style monotone functions: c- and a-analogs.
  -- -----------------------------------------------------------------------

  record CFunction {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      cfun : Policy → Time
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (τ (cfun c)) (τ (cfun d))
      step : ∀ c → QAdapter._≤s_ Q (τ (cfun (applyRG s c))) (τ (cfun c))

  record RGFixed {g : QAdapter.Scale Q} (s : RGStep g) (c : Policy) : Set (lsuc ℓ) where
    field
      le : _⊑_ (applyRG s c) c
      ge : _⊑_ c (applyRG s c)

  rg-μ-fixed
    : ∀ {g} (s : RGStep g)
    → ScottContinuous (Endo.fn (ClosureStepAt.endo s))
    → RGFixed s (rg-μ s)
  rg-μ-fixed s SC =
    record
      { le = rg-unfold-right s SC
      ; ge = rg-unfold-left s
      }

  record CFixedPointNormalization {g : QAdapter.Scale Q} (s : RGStep g) (F : CFunction s)
    : Set (lsuc (lsuc ℓ)) where
    field
      central : Time
      fixed≤ : ∀ {c} → RGFixed s c → QAdapter._≤s_ Q (τ (CFunction.cfun F c)) (τ central)
      fixed≥ : ∀ {c} → RGFixed s c → QAdapter._≤s_ Q (τ central) (τ (CFunction.cfun F c))

  c-fixed-point-central≤
    : ∀ {g} {s : RGStep g} {F : CFunction s}
    → (N : CFixedPointNormalization s F)
    → ∀ {c} → RGFixed s c
    → QAdapter._≤s_ Q (τ (CFunction.cfun F c)) (τ (CFixedPointNormalization.central N))
  c-fixed-point-central≤ N cfix =
    CFixedPointNormalization.fixed≤ N cfix

  c-fixed-point-central≥
    : ∀ {g} {s : RGStep g} {F : CFunction s}
    → (N : CFixedPointNormalization s F)
    → ∀ {c} → RGFixed s c
    → QAdapter._≤s_ Q (τ (CFixedPointNormalization.central N)) (τ (CFunction.cfun F c))
  c-fixed-point-central≥ N cfix =
    CFixedPointNormalization.fixed≥ N cfix

  record TimeSection : Set (lsuc (lsuc ℓ)) where
    field
      fromScale : QAdapter.Scale Q → Time
      τ-section : ∀ s → τ (fromScale s) ≡ s

  c-from-lyapunov
    : ∀ {g} {s : RGStep g}
    → TimeSection
    → RGLyapunov s
    → CFunction s
  c-from-lyapunov {s = s} TS L =
    record
      { cfun = λ c → TimeSection.fromScale TS (RGPotential.Φ (RGLyapunov.potential L) c)
      ; mono = λ {c} {d} le →
          let eqc = TimeSection.τ-section TS (RGPotential.Φ (RGLyapunov.potential L) c)
              eqd = TimeSection.τ-section TS (RGPotential.Φ (RGLyapunov.potential L) d)
          in subst (λ x → QAdapter._≤s_ Q x (τ (TimeSection.fromScale TS (RGPotential.Φ (RGLyapunov.potential L) d))))
                   (sym eqc)
                   (subst (λ y → QAdapter._≤s_ Q (RGPotential.Φ (RGLyapunov.potential L) c) y)
                          (sym eqd)
                          (RGPotential.mono (RGLyapunov.potential L) le))
      ; step = λ c →
          let eqc = TimeSection.τ-section TS (RGPotential.Φ (RGLyapunov.potential L) c)
              eqs = TimeSection.τ-section TS (RGPotential.Φ (RGLyapunov.potential L) (applyRG s c))
          in subst (λ x → QAdapter._≤s_ Q x (τ (TimeSection.fromScale TS (RGPotential.Φ (RGLyapunov.potential L) c))))
                   (sym eqs)
                   (subst (λ y → QAdapter._≤s_ Q (RGPotential.Φ (RGLyapunov.potential L) (applyRG s c)) y)
                          (sym eqc)
                          (RGLyapunov.decrease L c))
      }

  c-theorem-iter
    : ∀ {g} {s : RGStep g}
    → (F : CFunction s)
    → ∀ n → QAdapter._≤s_ Q
        (τ (CFunction.cfun F (rg-iter s (suc n))))
        (τ (CFunction.cfun F (rg-iter s n)))
  c-theorem-iter {s = s} F n = CFunction.step F (rg-iter s n)

  c-theorem-fixed
    : ∀ {g} {s : RGStep g} (F : CFunction s) (c : Policy)
    → _⊑_ (applyRG s c) c
    → QAdapter._≤s_ Q
        (τ (CFunction.cfun F (rg-μ s)))
        (τ (CFunction.cfun F c))
  c-theorem-fixed {s = s} F c pre =
    CFunction.mono F (rg-induction s c pre)

  record AFunction {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      afun : Policy → Time
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (τ (afun c)) (τ (afun d))
      step : ∀ c → QAdapter._≤s_ Q (τ (afun (applyRG s c))) (τ (afun c))
      tensor
        : ∀ c d → QAdapter._≤s_ Q
            (τ (afun (c ⊗∂ d)))
            (τ (QAdapter._+_ Q (afun c) (afun d)))
      unit : QAdapter._≤s_ Q (τ (afun I∂)) (τ (QAdapter.zero Q))

  record AFixedPointNormalization {g : QAdapter.Scale Q} (s : RGStep g) (F : AFunction s)
    : Set (lsuc (lsuc ℓ)) where
    field
      central : Time
      fixed≤ : ∀ {c} → RGFixed s c → QAdapter._≤s_ Q (τ (AFunction.afun F c)) (τ central)
      fixed≥ : ∀ {c} → RGFixed s c → QAdapter._≤s_ Q (τ central) (τ (AFunction.afun F c))

  a-fixed-point-central≤
    : ∀ {g} {s : RGStep g} {F : AFunction s}
    → (N : AFixedPointNormalization s F)
    → ∀ {c} → RGFixed s c
    → QAdapter._≤s_ Q (τ (AFunction.afun F c)) (τ (AFixedPointNormalization.central N))
  a-fixed-point-central≤ N cfix =
    AFixedPointNormalization.fixed≤ N cfix

  a-fixed-point-central≥
    : ∀ {g} {s : RGStep g} {F : AFunction s}
    → (N : AFixedPointNormalization s F)
    → ∀ {c} → RGFixed s c
    → QAdapter._≤s_ Q (τ (AFixedPointNormalization.central N)) (τ (AFunction.afun F c))
  a-fixed-point-central≥ N cfix =
    AFixedPointNormalization.fixed≥ N cfix

  a-theorem-iter
    : ∀ {g} {s : RGStep g}
    → (F : AFunction s)
    → ∀ n → QAdapter._≤s_ Q
        (τ (AFunction.afun F (rg-iter s (suc n))))
        (τ (AFunction.afun F (rg-iter s n)))
  a-theorem-iter {s = s} F n = AFunction.step F (rg-iter s n)

  a-theorem-fixed
    : ∀ {g} {s : RGStep g} (F : AFunction s) (c : Policy)
    → _⊑_ (applyRG s c) c
    → QAdapter._≤s_ Q
        (τ (AFunction.afun F (rg-μ s)))
        (τ (AFunction.afun F c))
  a-theorem-fixed {s = s} F c pre =
    AFunction.mono F (rg-induction s c pre)

  -- -----------------------------------------------------------------------
  -- Scaling dimensions (prequantale action on observables).
  -- -----------------------------------------------------------------------

  scalePow : ℕ → QAdapter.Scale Q → QAdapter.Scale Q
  scalePow zero a = QAdapter.e Q
  scalePow (suc n) a = QAdapter._·_ Q a (scalePow n a)

  record ScaleAction : Set (lsuc (lsuc ℓ)) where
    field
      act : QAdapter.Scale Q → QAdapter.Scale Q
      mono : ∀ {a b} → QAdapter._≤s_ Q a b → QAdapter._≤s_ Q (act a) (act b)
      mult : ∀ a b → act (QAdapter._·_ Q a b) ≡ QAdapter._·_ Q (act a) (act b)
      unit : act (QAdapter.e Q) ≡ QAdapter.e Q

  record ScalingDimension {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      action : ScaleAction
      obs : Policy → QAdapter.Scale Q
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ c → QAdapter._≤s_ Q
               (obs (applyRG s c))
               (QAdapter._·_ Q (ScaleAction.act action g) (obs c))

  scaling-step
    : ∀ {g} {s : RGStep g} (D : ScalingDimension s)
    → ∀ n → QAdapter._≤s_ Q
        (ScalingDimension.obs D (rg-iter s (suc n)))
        (QAdapter._·_ Q
          (ScaleAction.act (ScalingDimension.action D) g)
          (ScalingDimension.obs D (rg-iter s n)))
  scaling-step {s = s} D n =
    ScalingDimension.scale D (rg-iter s n)

  scaling-iter
    : ∀ {g} {s : RGStep g} (D : ScalingDimension s)
    → ∀ n → QAdapter._≤s_ Q
        (ScalingDimension.obs D (rg-iter s n))
        (QAdapter._·_ Q
          (scalePow n (ScaleAction.act (ScalingDimension.action D) g))
          (ScalingDimension.obs D (rg-iter s zero)))
  scaling-iter {g = g} {s = s} D zero =
    subst
      (λ x → QAdapter._≤s_ Q
        (ScalingDimension.obs D (rg-iter s zero))
        x)
      (sym (QAdapter.·-idl Q (ScalingDimension.obs D (rg-iter s zero))))
      (QAdapter.≤s-refl Q)
  scaling-iter {g = g} {s = s} D (suc n) =
    let actg = ScaleAction.act (ScalingDimension.action D) g
        obs0 = ScalingDimension.obs D (rg-iter s zero)
        step₁ = ScalingDimension.scale D (rg-iter s n)
        step₂ = QAdapter.·-mono Q (QAdapter.≤s-refl Q) (scaling-iter D n)
        step₃ =
          subst
            (λ x → QAdapter._≤s_ Q
              (QAdapter._·_ Q actg
                (QAdapter._·_ Q (scalePow n actg) obs0))
              x)
            (sym (QAdapter.·-assoc Q actg (scalePow n actg) obs0))
            (QAdapter.≤s-refl Q)
    in QAdapter.≤s-trans Q step₁ (QAdapter.≤s-trans Q step₂ step₃)

  -- Time-indexed RG flow (continuous-time analog).
  RGStepT : Time → Set (lsuc ℓ)
  RGStepT t = RGStep (τ t)

  castRG : ∀ {g g'} → g ≡ g' → RGStep g → RGStep g'
  castRG refl s = s

  rg-compose-time
    : ∀ {t u} → RGStepT t → RGStepT u → RGStepT (QAdapter._+_ Q t u)
  rg-compose-time {t} {u} s₁ s₂ =
    castRG (sym (QAdapter.τ-+ Q t u)) (rg-compose s₁ s₂)

  castRG-apply
    : ∀ {g g'} (eq : g ≡ g') (s : RGStep g) (c : Policy)
    → applyRG (castRG eq s) c ≡ applyRG s c
  castRG-apply refl s c = refl

  applyRG-compose
    : ∀ {g₁ g₂} (s₁ : RGStep g₁) (s₂ : RGStep g₂) (c : Policy)
    → applyRG (rg-compose s₁ s₂) c ≡ applyRG s₂ (applyRG s₁ c)
  applyRG-compose s₁ s₂ c = refl

  rg-compose-time-apply
    : ∀ {t u} (s₁ : RGStepT t) (s₂ : RGStepT u) (c : Policy)
    → applyRG (rg-compose-time s₁ s₂) c ≡ applyRG s₂ (applyRG s₁ c)
  rg-compose-time-apply {t = t} {u = u} s₁ s₂ c =
    trans
      (castRG-apply (sym (QAdapter.τ-+ Q t u)) (rg-compose s₁ s₂) c)
      (applyRG-compose s₁ s₂ c)

  record RGTimeFlowLike : Set (lsuc (lsuc ℓ)) where
    field
      step : (t : Time) → RGStepT t

  record RGTimeFlowLax : Set (lsuc (lsuc ℓ)) where
    field
      step : (t : Time) → RGStepT t
      unit≤ : _≤₂_ K (ClosureStepAt.endo (step (QAdapter.zero Q))) (idEndo K)
      comp≤ : ∀ t u
            → _≤₂_ K (ClosureStepAt.endo (step (QAdapter._+_ Q t u)))
                    (ClosureStepAt.endo (rg-compose-time (step t) (step u)))

  flowLike-from-lax : RGTimeFlowLax → RGTimeFlowLike
  flowLike-from-lax F =
    record { step = RGTimeFlowLax.step F }

  record RGTimeFlow : Set (lsuc (lsuc ℓ)) where
    field
      step : (t : Time) → RGStepT t
      unit≤ : _≤₂_ K (ClosureStepAt.endo (step (QAdapter.zero Q))) (idEndo K)
      comp≤ : ∀ t u
            → _≤₂_ K (ClosureStepAt.endo (step (QAdapter._+_ Q t u)))
                    (ClosureStepAt.endo (rg-compose-time (step t) (step u)))
      comp≥ : ∀ t u
            → _≤₂_ K (ClosureStepAt.endo (rg-compose-time (step t) (step u)))
                    (ClosureStepAt.endo (step (QAdapter._+_ Q t u)))

  flowLike-from-flow : RGTimeFlow → RGTimeFlowLike
  flowLike-from-flow F =
    record { step = RGTimeFlow.step F }

  record CFunctionTime (F : RGTimeFlowLike) : Set (lsuc (lsuc ℓ)) where
    field
      cfun : Policy → Time
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (τ (cfun c)) (τ (cfun d))
      step : ∀ t c → QAdapter._≤s_ Q
               (τ (cfun (applyRG (RGTimeFlowLike.step F t) c)))
               (τ (cfun c))

  record AFunctionTime (F : RGTimeFlowLike) : Set (lsuc (lsuc ℓ)) where
    field
      afun : Policy → Time
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (τ (afun c)) (τ (afun d))
      step : ∀ t c → QAdapter._≤s_ Q
               (τ (afun (applyRG (RGTimeFlowLike.step F t) c)))
               (τ (afun c))
      tensor : ∀ c d → QAdapter._≤s_ Q
               (τ (afun (c ⊗∂ d)))
               (τ (QAdapter._+_ Q (afun c) (afun d)))
      unit : QAdapter._≤s_ Q (τ (afun I∂)) (τ (QAdapter.zero Q))

  c-from-flow
    : ∀ {F : RGTimeFlowLike} → CFunctionTime F → (t : Time) → CFunction (RGTimeFlowLike.step F t)
  c-from-flow CF t =
    record
      { cfun = CFunctionTime.cfun CF
      ; mono = CFunctionTime.mono CF
      ; step = CFunctionTime.step CF t
      }

  a-from-flow
    : ∀ {F : RGTimeFlowLike} → AFunctionTime F → (t : Time) → AFunction (RGTimeFlowLike.step F t)
  a-from-flow AF t =
    record
      { afun = AFunctionTime.afun AF
      ; mono = AFunctionTime.mono AF
      ; step = AFunctionTime.step AF t
      ; tensor = AFunctionTime.tensor AF
      ; unit = AFunctionTime.unit AF
      }

  -- Beta-flow analogs (time-indexed RG generators on policies).
  record BetaFlow : Set (lsuc (lsuc ℓ)) where
    field
      beta : Time → Policy → Policy
      mono : ∀ t {c d} → _⊑_ c d → _⊑_ (beta t c) (beta t d)
      unit≤ : ∀ c → _⊑_ (beta (QAdapter.zero Q) c) c
      comp≤ : ∀ t u c → _⊑_ (beta (QAdapter._+_ Q t u) c) (beta u (beta t c))
      comp≥ : ∀ t u c → _⊑_ (beta u (beta t c)) (beta (QAdapter._+_ Q t u) c)

  beta-from-flow : ∀ (F : RGTimeFlow) → BetaFlow
  beta-from-flow F =
    record
      { beta = λ t c → applyRG (RGTimeFlow.step F t) c
      ; mono = λ t {c} {d} le →
          Endo.mono (ClosureStepAt.endo (RGTimeFlow.step F t)) le
      ; unit≤ = λ c → RGTimeFlow.unit≤ F c
      ; comp≤ = λ t u c →
          subst
            (λ x → _⊑_ (applyRG (RGTimeFlow.step F (QAdapter._+_ Q t u)) c) x)
            (rg-compose-time-apply (RGTimeFlow.step F t) (RGTimeFlow.step F u) c)
            (RGTimeFlow.comp≤ F t u c)
      ; comp≥ = λ t u c →
          subst
            (λ x → _⊑_ x (applyRG (RGTimeFlow.step F (QAdapter._+_ Q t u)) c))
            (rg-compose-time-apply (RGTimeFlow.step F t) (RGTimeFlow.step F u) c)
            (RGTimeFlow.comp≥ F t u c)
      }

  record ScalingDimensionTime (F : RGTimeFlowLike) : Set (lsuc (lsuc ℓ)) where
    field
      action : ScaleAction
      obs : Policy → QAdapter.Scale Q
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ t c → QAdapter._≤s_ Q
        (obs (applyRG (RGTimeFlowLike.step F t) c))
        (QAdapter._·_ Q (ScaleAction.act action (τ t)) (obs c))

  -- Optional information-theoretic refinements live in
  -- `LogOS.Packs.Agents.Experimental.Learning.RGFlow.Info`.
