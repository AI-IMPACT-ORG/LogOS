{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Dynamics.Action where

-- Time/scale dynamics as explicit (semi)group actions (refinement-first).
--
-- LogOS core `Flow` is a guarded closure (monotone + inflationary + lax-idempotent),
-- i.e. an *effective* / stabilised semantics doctrine.
--
-- Physical time evolution and RG scale evolution, however, are usually not idempotent
-- and may exhibit fixed points, convergence, and (in some models) cycles.
--
-- This module provides the minimal port vocabulary for those *dynamics*:
-- a monoid of parameters together with a monotone action on a boundary preorder.
--
-- The “two flows” story then becomes:
-- - one (possibly non-idempotent) action (time or scale dynamics), and
-- - one guarded closure `Flow` (EFT/effective semantics) that may be coherent
--   with the action (e.g. invariance under the dynamics, or commutation).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _≈_
  ; MonoOn
  )
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_; _⇒∂_)

-- --------------------------------------------------------------------------
-- A minimal monoid (S-tier laws: strict equalities as bookkeeping, not refinement).

record Monoid (ℓ : Level) : Set (lsuc ℓ) where
  infixl 6 _∙_
  field
    Carrier : Set ℓ
    _∙_     : Carrier → Carrier → Carrier
    ε       : Carrier

    assoc : ∀ a b c → ((a ∙ b) ∙ c) ≡ (a ∙ (b ∙ c))
    idl   : ∀ a → (ε ∙ a) ≡ a
    idr   : ∀ a → (a ∙ ε) ≡ a

open Monoid public

-- --------------------------------------------------------------------------
-- Monoid action on a boundary preorder (dynamics).

record ActionOnBoundary
  {ℓM ℓCon ℓRel : Level}
  (M : Monoid ℓM)
  (B : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓM ⊔ ℓCon ⊔ ℓRel)) where
  open Monoid M renaming (Carrier to Time; _∙_ to _∙M_; ε to εM)
  field
    step : Time → Con B → Con B

    -- Each time-slice is monotone in the boundary refinement preorder.
    step-mono : ∀ t → MonoOn B (step t)

    -- Action laws are stated up to mutual refinement (`≈`) on the boundary.
    step-ε≈id
      : ∀ c → _≈_ B (step εM c) c

    -- Right action convention: step (t ∙ u) = step u ∘ step t.
    step-∙≈comp
      : ∀ t u c → _≈_ B (step (t ∙M u) c) (step u (step t c))

open ActionOnBoundary public

-- --------------------------------------------------------------------------
-- Monoid action on a kernel (time-evolution on code + coherent boundary effect).
--
-- This is the smallest interface that supports:
-- - trajectories (iterate/end by time parameter),
-- - cycles (step t ≈ id on some observable), and
-- - reduction to boundary dynamics via `decode-mapCode`.

record ActionOnKernel
  {ℓM ℓKernelCon ℓKernelRel ℓCode : Level}
  (M : Monoid ℓM)
  (K : Kernel ℓKernelCon ℓKernelRel ℓCode)
  : Set (lsuc (ℓM ⊔ ℓKernelCon ⊔ ℓKernelRel ⊔ ℓCode)) where
  open Monoid M renaming (Carrier to Time; _∙_ to _∙M_; ε to εM)
  field
    stepK : Time → KernelHom K K

    -- Laws in LOG’s boundary-driven observational preorder (`_⇒∂_`) on kernel morphisms.
    --
    -- `≈` on `KernelHom` is definable as mutual refinement, but we keep it
    -- expanded to avoid importing the whole LOG layer here.
    stepK-ε⇒id : stepK εM ⇒∂ idKernelHom K
    stepK-id⇒ε : idKernelHom K ⇒∂ stepK εM

    stepK-∙⇒comp : ∀ t u → stepK (t ∙M u) ⇒∂ (stepK u ∘ stepK t)
    stepK-comp⇒∙ : ∀ t u → (stepK u ∘ stepK t) ⇒∂ stepK (t ∙M u)

open ActionOnKernel public

-- --------------------------------------------------------------------------
-- Optional: commutation of two dynamics on the same boundary (e.g. time vs scale).

record CommuteBoundaryActions
  {ℓM₁ ℓM₂ ℓCon ℓRel : Level}
  {B : ConPreorder ℓCon ℓRel}
  {M₁ : Monoid ℓM₁}
  {M₂ : Monoid ℓM₂}
  (A₁ : ActionOnBoundary M₁ B)
  (A₂ : ActionOnBoundary M₂ B)
  : Set (lsuc (ℓM₁ ⊔ ℓM₂ ⊔ ℓCon ⊔ ℓRel)) where
  field
    commutes
      : ∀ t u c
      → _≈_ B
          (step A₁ t (step A₂ u c))
          (step A₂ u (step A₁ t c))

open CommuteBoundaryActions public
