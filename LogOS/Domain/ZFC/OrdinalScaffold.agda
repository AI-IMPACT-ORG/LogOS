{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.OrdinalScaffold where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import Data.Ordinal as Ord
open import LogOS.Domain.SetTheory.Cumulative
open import LogOS.Domain.SetTheory.CumulativeSurface using (stageToSurface)
open import LogOS.Domain.SetTheory.LimitPack
open import LogOS.Domain.SetTheory.Dsl using (ZFDsl)

-- Experimental ordinal-flavoured stage index -----------------------------------
--
-- This module packages an ordinal-indexed stage scaffold as explicit
-- assumptions. It is not required for the production WFGraph ZF/ZFC route.
--
-- We parameterise stages by the simple Ord type imported from Data.Ordinal.
-- Limit ordinals collapse to the distinguished ω; the aim is a compact stage
-- index that still exposes the structure an ordinal-tower build would require.

Ord-isSucc : Ord.Ord → Set
Ord-isSucc (Ord.fin zero) = ⊥
Ord-isSucc (Ord.fin (suc _)) = ⊤
Ord-isSucc Ord.ω = ⊤

Ord-isLim : Ord.Ord → Set
Ord-isLim (Ord.fin zero) = ⊥
Ord-isLim (Ord.fin (suc _)) = ⊥
Ord-isLim Ord.ω = ⊤

fin≤succ : ∀ n → Ord._≤_ (Ord.fin n) (Ord.succ (Ord.fin n))
fin≤succ n = Ord.≤ℕ-suc n

leJoin-left : ∀ i j → Ord._≤_ i (Ord.join i j)
leJoin-left (Ord.fin m) (Ord.fin n) = Ord.≤ℕ-max-left m n
leJoin-left (Ord.fin _) Ord.ω = tt
leJoin-left Ord.ω _ = tt

leJoin-right : ∀ i j → Ord._≤_ j (Ord.join i j)
leJoin-right (Ord.fin m) (Ord.fin n) = Ord.≤ℕ-max-right m n
leJoin-right (Ord.fin _) Ord.ω = tt
leJoin-right Ord.ω (Ord.fin _) = tt
leJoin-right Ord.ω Ord.ω = tt

OrdinalStageIndex : StageIndex
OrdinalStageIndex = record
  { I      = Ord.Ord
  ; _≤_    = Ord._≤_
  ; isSucc = Ord-isSucc
  ; isLim  = Ord-isLim
  ; zeroStage   = Ord.fin (suc zero)
  ; zero-isSucc = tt
  ; join   = λ i j → Ord.join i j , (leJoin-left i j , leJoin-right i j)
  ; succAbove = λ i →
      let s = Ord.succ i
      in s , (succIsSucc i , succWitness i)
  }
  where
    succIsSucc : ∀ i → Ord-isSucc (Ord.succ i)
    succIsSucc (Ord.fin zero) = tt
    succIsSucc (Ord.fin (suc _)) = tt
    succIsSucc Ord.ω = tt
    succWitness : ∀ i → Ord._≤_ i (Ord.succ i)
    succWitness (Ord.fin n) = fin≤succ n
    succWitness Ord.ω = tt

-- Ordinal stage data (scaffold) ------------------------------------------------
-- The remaining packs (StageSet, closures, rank bounding, Scott choice, and the
-- cumulative hierarchy itself) are packaged as an explicit record of
-- assumptions rather than postulates. Once these fields are implemented the
-- helper below immediately produces a StageToCH value and a tensor/endomap DSL surface.

record OrdinalStageCommon (ℓ : Level) : Set (lsuc ℓ) where
  field
    StageSetᵒ  : StageSet {ℓU = ℓ} OrdinalStageIndex
    Successorᵒ : SuccessorClosure {ℓU = ℓ} OrdinalStageIndex StageSetᵒ
    Limitᵒ     : LimitClosure {ℓU = ℓ} OrdinalStageIndex StageSetᵒ
    Rankᵒ      : RankBounding {ℓU = ℓ} OrdinalStageIndex StageSetᵒ

record OrdinalHierarchy {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                        (K : Kernel Sig Q)
                        : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  private
    module Bnd = ConPoset (BulkBoundary.bnd BB)
  field
    common       : OrdinalStageCommon ℓ
    CH∞          : CumulativeHierarchy K
    realise∞ᵒ    : CumulativeHierarchy.SetU CH∞ → Bnd.Con
    mem⇒flow∞ᵒ   : ∀ {x y} → CumulativeHierarchy._∈_ CH∞ x y
                  → Bnd._⊑_ (realise∞ᵒ x) (Endo.fn (Flow-Endo K) (realise∞ᵒ y))
    eq⇒realise∞≡ᵒ : ∀ {x y} → CumulativeHierarchy._≈_ CH∞ x y → realise∞ᵒ x ≡ realise∞ᵒ y
    flow-stable∞ᵒ : ∀ x → Bnd._⊑_ (Endo.fn (Flow-Endo K) (realise∞ᵒ x)) (realise∞ᵒ x)

  open OrdinalStageCommon common

  StageToCHᵒ : StageToCH K
  StageToCHᵒ = record
    { S   = OrdinalStageIndex
    ; SS  = StageSetᵒ
    ; SC  = Successorᵒ
    ; LC  = Limitᵒ
    ; RB  = Rankᵒ
    ; CH  = CH∞
    ; realise∞     = realise∞ᵒ
    ; mem⇒flow∞    = mem⇒flow∞ᵒ
    ; eq⇒realise∞≡ = eq⇒realise∞≡ᵒ
    ; tf-stable∞   = flow-stable∞ᵒ
    }

OrdinalSurface
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (plan : OrdinalHierarchy K)
  → ZFDsl K
OrdinalSurface K plan = stageToSurface K (OrdinalHierarchy.StageToCHᵒ plan)
