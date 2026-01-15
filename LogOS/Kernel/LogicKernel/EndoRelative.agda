{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.EndoRelative where

-- Closure-step calculus relative to an arbitrary modality/endomap `J`.
--
-- This generalises the Flow-specialised DSL in `LogicKernel.Endo`:
-- - pick any endomap `J` on boundary constraints,
-- - assume it is a (lax) closure: `id ≤ J` and `J ∘ J ≤ J`,
-- - then “closure steps” (id ≤ f ≤ J) compose and can be “closed” by whiskering with `J`.
--
-- This is the right abstraction boundary for nuclei/modality-style reasoning
-- (forcing, publicisation, feasibility, auditability), without committing to the
-- kernel’s distinguished fixed point `Th*`.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax; mono)

open import LogOS.Kernel.LogicKernel using (LogicKernel; module LogicKernel)
open import LogOS.Kernel.LogicKernel.EndoCore
  using
    ( Endo; _≤₂_; idEndo; _∘E_
    ; refl₂; trans₂
    )

open Endo public

module With
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : LogicKernel Sig Q)
  (J   : Endo K)
  (id≤J : _≤₂_ K (idEndo K) J)
  (J∘J≤J : _≤₂_ K (J ∘E J) J)
  where

  open LogicKernel K

  private
    CP : ConPoset ℓ
    CP = BulkBoundary.bnd BB

  -- “Apply f, then take J-shadow”.
  J-closeEndo : Endo K → Endo K
  J-closeEndo f = J ∘E f

  id≤J-close
    : ∀ (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K (idEndo K) (J-closeEndo f)
  id≤J-close f id≤f = λ c →
    ConPoset.trans CP (id≤f c) (id≤J (Endo.fn f c))

  J-close≤J
    : ∀ (f : Endo K)
    → _≤₂_ K f J
    → _≤₂_ K (J-closeEndo f) J
  J-close≤J f f≤J = λ c →
    let
      step₁ = Endo.mono J (f≤J c)   -- J(f c) ≤ J(J c)
      step₂ = J∘J≤J c               -- J(J c) ≤ J c
    in ConPoset.trans CP step₁ step₂

  J≤J-close
    : ∀ (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K J (J-closeEndo f)
  J≤J-close f id≤f = λ c → Endo.mono J (id≤f c)

  -- Closure steps relative to `J`: endomaps with `id ≤ f ≤ J`.

  record ClosureStep : Set (lsuc ℓ) where
    field
      endo  : Endo K
      infl  : _≤₂_ K (idEndo K) endo
      leJ   : _≤₂_ K endo J

  open ClosureStep public

  mkClosureStep
    : (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f J
    → ClosureStep
  mkClosureStep f infl leJ = record { endo = f ; infl = infl ; leJ = leJ }

  J-closeStep : ClosureStep → ClosureStep
  J-closeStep s =
    mkClosureStep
      (J-closeEndo (endo s))
      (id≤J-close (endo s) (infl s))
      (J-close≤J (endo s) (leJ s))

  _∘Step_ : ClosureStep → ClosureStep → ClosureStep
  _∘Step_ s₂ s₁ =
    let
      f = endo s₁
      g = endo s₂

      inflComp : _≤₂_ K (idEndo K) (g ∘E f)
      inflComp = λ c → ConPoset.trans CP (infl s₁ c) (infl s₂ (Endo.fn f c))

      leJComp : _≤₂_ K (g ∘E f) J
      leJComp = λ c →
        let
          step₁ = leJ s₂ (Endo.fn f c)            -- g(f c) ≤ J(f c)
          step₂ = Endo.mono J (leJ s₁ c)          -- J(f c) ≤ J(J c)
          step₃ = J∘J≤J c                         -- J(J c) ≤ J c
        in ConPoset.trans CP step₁ (ConPoset.trans CP step₂ step₃)
    in
    mkClosureStep (g ∘E f) inflComp leJComp

  infixr 9 _∘Step_

  -- Left-to-right composition (operand order matches execution order).
  _thenStep_ : ClosureStep → ClosureStep → ClosureStep
  _thenStep_ s₁ s₂ = s₂ ∘Step s₁

  infixl 9 _thenStep_

-- Helper: build a relative-closure DSL directly from a `ClosureOp` on the
-- boundary preorder.

module FromClosureOp
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : LogicKernel Sig Q)
  (C   : ClosureOp (BulkBoundary.bnd (LogicKernel.BB K)))
  where

  open LogicKernel K

  J : Endo K
  J =
    record
      { fn   = cl C
      ; mono = mono C
      }

  id≤J : _≤₂_ K (idEndo K) J
  id≤J = infl C

  J∘J≤J : _≤₂_ K (J ∘E J) J
  J∘J≤J = idemp-lax C

  module Rel = With K J id≤J J∘J≤J
