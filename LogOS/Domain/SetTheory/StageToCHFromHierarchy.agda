{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.SetTheory.StageToCHFromHierarchy where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ¬_; ⊥)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Endo using (Th⋆K; Th⋆≤FlowTh⋆; FlowTh⋆≤Th⋆)

open import Data.Nat using (ℕ; zero; suc)
open import Data.NatOrder as NatOrder using (_≤ℕ_; z≤n; s≤s)
open import Data.NatExtra using (_⊔ℕ_; max-left; max-right; ≤ℕ-suc)

open import LogOS.Domain.SetTheory.Cumulative
open import LogOS.Domain.SetTheory.LimitPack using (CumulativeHierarchy)

-- A very small, LogOS-native way to obtain a `StageToCH` from any already-built
-- cumulative hierarchy:
--
-- - stages are indexed by ℕ (successor-only; no limit stages),
-- - every stage contains the same universe `SetU`,
-- - embeddings are identity (since stages are constant),
-- - boundary realisation uses the kernel’s canonical least fixed point `Th⋆K`,
--   so the Flow obligations are discharged uniformly.
--
-- This keeps staging as a *presentation layer* while preserving soundness and
-- reusing existing ZF/ZFC interpretations (e.g. the WF-graph development).

private
  -- Reflexivity of the project’s ℕ-order.
  ≤ℕ-refl : ∀ n → n ≤ℕ n
  ≤ℕ-refl zero = z≤n
  ≤ℕ-refl (suc n) = s≤s (≤ℕ-refl n)

StageIndexℕ⁺ : StageIndex
StageIndexℕ⁺ = record
  { I      = ℕ
  ; _≤_    = _≤ℕ_
  ; isSucc = λ _ → ⊤
  ; isLim  = λ _ → ⊥
  ; zeroStage   = zero
  ; zero-isSucc = tt
  ; join   = λ i j → (i ⊔ℕ j) , (max-left i j , max-right i j)
  ; succAbove = λ i → suc i , (tt , ≤ℕ-suc i)
  }

StageToCH-fromCH
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (CH : CumulativeHierarchy K)
  → StageToCH K
StageToCH-fromCH {ℓ = ℓ} K CH = record
  { S   = StageIndexℕ⁺
  ; SS  = SS
  ; SC  = SC
  ; LC  = LC
  ; RB  = RB
  ; CH  = CH
  ; realise∞     = λ _ → Th⋆K K
  ; mem⇒flow∞    = λ _ → Th⋆≤FlowTh⋆ K
  ; eq⇒realise∞≡ = λ _ → refl
  ; tf-stable∞   = λ _ → FlowTh⋆≤Th⋆ K
  }
  where
    open CumulativeHierarchy CH

    SS : StageSet {ℓU = ℓ} StageIndexℕ⁺
    SS = record
      { U      = λ _ → SetU
      ; _∈ᵢ_   = λ {_} → _∈_
      ; _≈ᵢ_   = λ {_} → _≈_
      ; refl≈ᵢ  = λ {_} → refl≈
      ; sym≈ᵢ   = λ {_} → sym≈
      ; trans≈ᵢ = λ {_} → trans≈
      ; extensionalityᵢ = λ {_} → extensionality
      ; mem-extᵢ        = λ {_} → mem-ext
      ; emb    = λ _ x → x
      ; emb-∈  = λ _ p → p
      ; emb-≈  = λ _ e → e
      }

    SC : SuccessorClosure {ℓU = ℓ} StageIndexℕ⁺ SS
    SC = record
      { emptyᵢ    = λ {_} _ → empty
      ; pairingᵢ  = λ {_} _ → pairing
      ; unionᵢ    = λ {_} _ → union
      ; powersetᵢ = λ {_} _ → powerset
      }

    LC : LimitClosure {ℓU = ℓ} StageIndexℕ⁺ SS
    LC = record
      { unionLim = λ {_} () }

    RB : RankBounding {ℓU = ℓ} StageIndexℕ⁺ SS
    RB = record
      { separationᵢ  = λ {i} P x →
          ((i , ≤ℕ-refl i) , (proj₁ (separation P x) , λ z → proj₂ (separation P x) z))
      ; replacementᵢ = λ {i} F x →
          ((i , ≤ℕ-refl i) , (proj₁ (replacement F x) , λ z → proj₂ (replacement F x) z))
      }
