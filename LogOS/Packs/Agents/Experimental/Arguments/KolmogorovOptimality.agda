{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality where

-- Reusable core: Kolmogorov/Solomonoff-style optimality and its LogOS-native
-- publicisation (`Pr`) via the generic observer calculus.
--
-- This module is intentionally independent of ωCPO / RG infrastructure. Packs
-- that require scaling arguments can add those assumptions on top.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPoset)
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded as GK
import LogOS.Theorems.Meta.MathPhysSynthesis as MPS

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : GradedKernel Sig Q)
  where

  open GradedKernel K public using (Code; decode; reify; reify-decode)

  Dec : Set ℓ
  Dec = ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K))

  -- Kolmogorov/Solomonoff optimality relative to a code-size model.
  KOptimal : (Code → ℕ) → Code → Set ℓ
  KOptimal size γ =
    ∀ δ → decode δ ≡ decode γ → size γ ≤ℕ size δ

  -- Publicised/stable fragment of KOptimal.
  module Obs (size : Code → ℕ) where
    module O = MPS.Observer Code Dec decode (GK.FlowCode K) (KOptimal size)

    DiscoverCode : Code → Set (lsuc (lsuc ℓ))
    DiscoverCode = O.Pr

    discover-reify
      : ∀ γ → DiscoverCode (reify γ) ↔ DiscoverCode γ
    discover-reify γ =
      let eq = reify-decode γ in
      record
        { to   = λ d → O.Pr-ext (reify γ) γ eq d
        ; from = λ d → O.Pr-ext γ (reify γ) (sym eq) d
        }

    -- Maximality: any admissible observer predicate factors through DiscoverCode.
    discover-largest
      : (Obs : Code → Set (lsuc ℓ))
      → O.AdmissibleObs {ℓO = lsuc ℓ} Obs
      → ∀ {γ} → Obs γ → DiscoverCode γ
    discover-largest Obs A oγ = Obs , (A , oγ)

    open O public using
      ( Pr-ext
      ; Pr-stable
      ; Pr-sound
      )
