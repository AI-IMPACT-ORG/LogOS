{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetTheory.StageToCHFromHierarchy where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ¬_; ⊥)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo using (Endo; Flow-Endo; Th⋆K; Th⋆≤FlowTh⋆; FlowTh⋆≤Th⋆; id≤Flow)

open import Data.Nat using (ℕ; zero; suc)
open import Data.NatOrder as NatOrder using (_≤ℕ_; z≤n; s≤s)
open import Data.NatExtra using (_⊔ℕ_; max-left; max-right; ≤ℕ-suc)

open import LogOS.Domain.ZFC.SetTheory.Cumulative
open import LogOS.Domain.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)

-- A very small, LogOS-native way to obtain a `StageToCH` from any already-built
-- cumulative hierarchy:
--
-- - stages are indexed by ℕ (successor-only; no limit stages),
-- - every stage contains the same universe `SetU`,
-- - embeddings are identity (since stages are constant),
-- - boundary realisation uses the kernel’s canonical fixed-point witness `Th⋆K`,
--   so the Flow obligations are discharged uniformly (no leastness claim here).
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

private
  module Common
    {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (CH : CumulativeHierarchy K)
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

StageToCH-fromCH
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (CH : CumulativeHierarchy K)
  → StageToCH K
StageToCH-fromCH {ℓ = ℓ} K CH =
  let module C = Common {ℓ = ℓ} K CH in
  record
    { S   = StageIndexℕ⁺
    ; SS  = C.SS
    ; SC  = C.SC
    ; LC  = C.LC
    ; RB  = C.RB
    ; CH  = CH
    ; realise∞     = λ _ → Th⋆K K
    ; mem⇒flow∞    = λ _ → Th⋆≤FlowTh⋆ K
    ; eq⇒realise∞≡ = λ _ → refl
    ; tf-stable∞   = λ _ → FlowTh⋆≤Th⋆ K
    }

-- Optional variant: if a kernel supplies an explicit boundary ωCPO + a
-- FiniteFirst (Scott-continuity) witness for Flow, we can use the Kleene μ of
-- Flow (rather than the distinguished witness `Th⋆K`) as the infinity-stage
-- realisation. This supports “least fixed point / least model” style claims,
-- but keeps all extra structure explicit.

StageToCH-fromCH-μFlow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (CH : CumulativeHierarchy K)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO)
              (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst)
              (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
  → StageToCH K
StageToCH-fromCH-μFlow {ℓ = ℓ} {Sig = Sig} {Q = Q} K CH ωCPO FF =
  record
    { S   = StageIndexℕ⁺
    ; SS  = C.SS
    ; SC  = C.SC
    ; LC  = C.LC
    ; RB  = C.RB
    ; CH  = CH
    ; realise∞     = λ _ → μFlow
    ; mem⇒flow∞    = λ _ → μ≤Flowμ
    ; eq⇒realise∞≡ = λ _ → refl
    ; tf-stable∞   = λ _ → Flowμ≤μ
    }
  where
    module C = Common {ℓ = ℓ} K CH
    module GT = Truth.GuardedTruth Sig Q
    module μ = GT.Kleene ωCPO

    private
      CP = BulkBoundary.bnd (Kernel.BB K)

      FlowSat : ConPoset.Con CP → ConPoset.Con CP
      FlowSat = Endo.fn (Flow-Endo K)

      μFlow : ConPoset.Con CP
      μFlow = μ.μ FlowSat

      μ≤Flowμ : ConPoset._⊑_ CP μFlow (FlowSat μFlow)
      μ≤Flowμ = μ.μ-unfold-left FlowSat (Endo.mono (Flow-Endo K))

      -- Build the Scott-continuity record for Flow from the FiniteFirst witness.
      SCFlow : μ.ScottContinuous FlowSat
      SCFlow = record { cont-ω = Truth.GuardedCore.FiniteFirst.cont-ω FF }

      inflFlow : ∀ c → ConPoset._⊑_ CP c (FlowSat c)
      inflFlow = id≤Flow K

      Flowμ≤μ : ConPoset._⊑_ CP (FlowSat μFlow) μFlow
      Flowμ≤μ = μ.μ-unfold-right-infl FlowSat SCFlow inflFlow
