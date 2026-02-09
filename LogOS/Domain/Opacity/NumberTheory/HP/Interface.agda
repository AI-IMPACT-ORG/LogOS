{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.HP.Interface where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Computation.EvolutionOperator using (EvolOperator)

-- Minimal, ring-free Hilbert–Pólya interface tied only to a Kernel.

record HPInterface {ℓ : Level}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : Kernel Sig Q)
                   : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  private
    Con∂ : Set ℓ
    Con∂ = ConPreorder.Con (BulkBoundary.bnd BB)

  field
    H        : Set ℓ
    Op       : H → H
    embed    : Con∂ → H
    intertwine : ∀ c → embed (Endo.fn (Flow-Endo K) c)
                          ≡ Op (embed c)

  -- Canonical view: HPInterface is an evolution operator for the boundary Flow endomap.
  asEvolOperator : EvolOperator {ℓC = ℓ} {ℓH = ℓ} Con∂ (Endo.fn (Flow-Endo K))
  asEvolOperator = record
    { H          = H
    ; embed      = embed
    ; Op         = Op
    ; intertwine = intertwine
    }

-- Faithful embedding: reflect equalities back to boundary constraints.

record EmbedFaithful {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K   : Kernel Sig Q)
                     (HP  : HPInterface K)
                     : Set (lsuc ℓ) where
  open Kernel K
  open HPInterface HP
  field
    embed-reflects≡ : ∀ {c d : ConPreorder.Con (BulkBoundary.bnd BB)}
                      → embed c ≡ embed d → c ≡ d

-- Helper: build faithfulness from a right-inverse (retract) π of embed.
-- If π ∘ embed ≡ id on boundary constraints, then equality on H reflects to equality on boundary.

embedFaithful-from-retract
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
    → (π : HPInterface.H HP → ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K)))
    → (∀ c → π (HPInterface.embed HP c) ≡ c)
    → EmbedFaithful K HP
embedFaithful-from-retract K HP π right = record
  { embed-reflects≡ = λ {c}{d} eq →
      let open Kernel K in
      let open HPInterface HP in
      trans (sym (right c)) (trans (cong π eq) (right d))
  }

-- Special case: identity-like embeddings (when H is judgmentally the boundary and embed = id).
--
-- Note: an identity-like special case follows from embedFaithful-from-retract
-- when `H` is judgmentally the boundary and `embed = id`.
