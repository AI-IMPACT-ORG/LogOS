{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Halting where

open import LogOS.Prelude
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Syntax.Prop using (_↔_; ¬_; intro; ⊥)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Computation.Core as CompCore
open import LogOS.Computation.FromKernel

open import LogOS.Theorems.Meta.Base using (DeciderC)
open import LogOS.Theorems.Meta.Assumptions.Diagonal as A

-- Halting undecidability (classical shape):
-- Given a computation on codes and a recursion/diagonalization principle
-- producing a liar for any decidable predicate, there is no total decider for Halts.

noDecider-Halting
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HM : A.HaltingModel K)
    (HD : A.HaltingDiagonal K HM)
  → ¬ (DeciderC {Sig = Sig} {Q = Q} {K = K}
        (λ γ → CompCore.Computation.Halts (A.HaltingModel.Comp HM) γ))
noDecider-Halting K HM HD dec =
  let open A.HaltingModel HM in
  let open CompCore.Computation Comp renaming (Halts to HaltsC) in
  let pair = A.HaltingDiagonal.liarForDecider HD (DeciderC.decide dec) (DeciderC.total dec)
      L    = proj₁ pair
      eq   = proj₂ pair
      d?   = DeciderC.total dec L
  in helper L eq d?
  where
  helper
    : (L : Kernel.Code K)
    → (CompCore.Computation.Halts (A.HaltingModel.Comp HM) L ↔ ¬ (DeciderC.decide dec L))
    → (DeciderC.decide dec L ⊎ ¬ (DeciderC.decide dec L))
    → ⊥
  helper L eq (inj₁ dL) =
    let hL  = DeciderC.sound dec L dL
        ndL = _↔_.to eq hL
    in ndL dL
  helper L eq (inj₂ ndL) =
    let hL  = _↔_.from eq ndL
        dL' = DeciderC.comp dec L hL
    in ndL dL'

-- Convenience: use the canonical computation derived from a kernel
-- (Guard ∘ Body; Halts is a model-chosen predicate as per FromKernel).

noDecider-Halting-FromKernel
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K  : Kernel Sig Q)
    (HD : A.HaltingDiagonal K (record { Comp = (let module FK = FromKernel Sig Q K in FK.Comp) }))
  → ¬ (DeciderC {Sig = Sig} {Q = Q} {K = K}
        (λ γ → CompCore.Computation.Halts (let module FK = FromKernel Sig Q K in FK.Comp) γ))
noDecider-Halting-FromKernel Sig Q K HD =
  noDecider-Halting K (record { Comp = (let module FK = FromKernel Sig Q K in FK.Comp) }) HD
