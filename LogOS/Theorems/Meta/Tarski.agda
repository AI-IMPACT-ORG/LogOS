{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Tarski where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥; _↔_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Theorems.Meta.Base using (DeciderC)
open import LogOS.Theorems.Meta.Assumptions.Diagonal as A
open import LogOS.Theorems.Meta.Full as F
open import LogOS.Kernel.Hom

-- Transport shape (textbook reduction lemma):
-- if the pullback of TruthK along the canonical fold has no total decider on the
-- canonical FreeKernel, then TruthK has no total decider on K.

undef-transport
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : F.WorldH Sig Q)
    (K  : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓ)
  → ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
         (λ γ → TruthK (KernelHom.mapCode (F.foldTo Sig Q HW K) γ)))
  → ¬ (DeciderC {K = K} TruthK)
undef-transport HW K TruthK freeNoDecider =
  F.noDecider-transport HW K TruthK freeNoDecider

-- Liar-style undefinability against deciders:
-- If for every decidable predicate P there exists a self-referential γ with
-- TruthK γ ↔ ¬ P γ, then no total decider exists for TruthK.


undef-classical
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓ)
    (TD : A.TruthDiagonal K TruthK)
  → ¬ (DeciderC {Sig = Sig} {Q = Q} {K = K} TruthK)
undef-classical K TruthK TD dec =
  let pair = A.TruthDiagonal.liarForDecider TD (DeciderC.decide dec) (DeciderC.total dec)
      γ    = proj₁ pair
      eq   = proj₂ pair
  in
  let d? = DeciderC.total dec γ in
  helper γ eq d?
  where
  helper
    : (γ : Kernel.Code K)
    → ((TruthK γ) ↔ (¬ (DeciderC.decide dec γ)))
    → (DeciderC.decide dec γ ⊎ ¬ (DeciderC.decide dec γ))
    → ⊥
  helper γ eq (inj₁ dγ) =
    let tγ = DeciderC.sound dec γ dγ
        ndγ = _↔_.to eq tγ
    in ndγ dγ
  helper γ eq (inj₂ ndγ) =
    let tγ  = _↔_.from eq ndγ
        dγ' = DeciderC.comp dec γ tγ
    in ndγ dγ'
