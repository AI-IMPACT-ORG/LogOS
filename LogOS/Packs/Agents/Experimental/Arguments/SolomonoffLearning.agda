{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.SolomonoffLearning where

-- Solomonoff-style learning, in the minimal “LogOS-native” sense.
--
-- This module does *not* attempt to build a numeric probability measure.
-- Instead it packages the standard Solomonoff/Kolmogorov lens:
--
--   “prefer the shortest description consistent with observations”
--
-- as a predicate on codes, and then applies the observer/publicisation operator
-- `Pr` to make it:
-- - decode-extensional (representation invariant), and
-- - stable under the kernel’s one-step dynamics (RG/FlowCode).
--
-- Concretely, we use the generic observer calculus (`MathPhysSynthesis.Observer`)
-- and instantiate it at the graded-kernel code language and its `FlowCode` step.

open import LogOS.Prelude

open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Prelude.Nat using (ℕ)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded as GK
import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality as KOpt

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : GradedKernel Sig Q)
  where

  module KO = KOpt.For K
  open KO using (Code; decode; reify; reify-decode; Dec)

  -- Solomonoff/Kolmogorov optimality predicate:
  -- γ is optimal if it has minimal size among codes with the same decode.
  SolomonoffOptimal : (Code → ℕ) → Code → Set ℓ
  SolomonoffOptimal = KO.KOptimal

  -- Publicised/stable fragment of Solomonoff optimality.
  --
  -- `Solomonoff size γ` is `Pr (SolomonoffOptimal size) γ` in the observer calculus:
  -- it is the maximal admissible, decode-extensional, FlowCode-stable predicate
  -- contained in optimality.
  module Solomonoff (size : Code → ℕ) where
    module O = KO.Obs size

    Solomonoff : Code → Set (lsuc (lsuc ℓ))
    Solomonoff = O.DiscoverCode

    solomonoff-reify : ∀ γ → Solomonoff (reify γ) ↔ Solomonoff γ
    solomonoff-reify = O.discover-reify

    solomonoff-stable : ∀ γ → Solomonoff γ ↔ Solomonoff (GK.FlowCode K γ)
    solomonoff-stable = O.Pr-stable

    solomonoff-sound : ∀ {γ} → Solomonoff γ → SolomonoffOptimal size γ
    solomonoff-sound = O.Pr-sound

    open O public using
      ( Pr-ext
      ; Pr-stable
      ; Pr-sound
      )
