{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.EndoFixedPointCore where

open import LogOS.Prelude

record KleeneOps {ℓ : Level} (Con : Set ℓ) : Set (lsuc (lsuc ℓ)) where
  infix 4 _⊑_
  field
    _⊑_ : Con → Con → Set ℓ
    MonoOn : (Con → Con) → Set ℓ

    iter : (Con → Con) → ℕ → Con
    μF   : (Con → Con) → Con

    μF-unfold-left
      : (F : Con → Con)
      → MonoOn F
      → _⊑_ (μF F) (F (μF F))

    μF-induction
      : (F : Con → Con)
      → MonoOn F
      → ∀ c → _⊑_ (F c) c → _⊑_ (μF F) c

    ScottContinuous : (Con → Con) → Set (lsuc ℓ)

    μF-unfold-right
      : (F : Con → Con)
      → ScottContinuous F
      → (∀ n → _⊑_ (iter F n) (iter F (suc n)))
      → _⊑_ (F (μF F)) (μF F)

    iter-mono-chain-infl
      : (F : Con → Con)
      → (infl : ∀ c → _⊑_ c (F c))
      → ∀ n → _⊑_ (iter F n) (iter F (suc n))

    μF-unfold-right-infl
      : (F : Con → Con)
      → ScottContinuous F
      → (infl : ∀ c → _⊑_ c (F c))
      → _⊑_ (F (μF F)) (μF F)

record EndoOps {ℓCon ℓEndo : Level}
  (Con : Set ℓCon)
  (_⊑_ : Con → Con → Set ℓCon)
  (MonoOn : (Con → Con) → Set ℓCon)
  : Set (lsuc (ℓCon ⊔ ℓEndo)) where
  field
    Endo : Set ℓEndo
    fn   : Endo → Con → Con
    mono : (f : Endo) → MonoOn (fn f)

module For
  {ℓCon ℓEndo : Level}
  {Con : Set ℓCon}
  (K : KleeneOps Con)
  (E : EndoOps {ℓEndo = ℓEndo} Con (KleeneOps._⊑_ K) (KleeneOps.MonoOn K))
  where

  open KleeneOps K public
  open EndoOps E public using (Endo; fn; mono)

  Policy : Set _
  Policy = Con

  iterEndo : Endo → ℕ → Policy
  iterEndo f = iter (fn f)

  muEndo : Endo → Policy
  muEndo f = μF (fn f)

  muEndo-unfold-left
    : (f : Endo)
    → _⊑_ (muEndo f) (fn f (muEndo f))
  muEndo-unfold-left f = μF-unfold-left (fn f) (mono f)

  muEndo-induction
    : (f : Endo) (c : Policy)
    → _⊑_ (fn f c) c
    → _⊑_ (muEndo f) c
  muEndo-induction f c pre =
    μF-induction (fn f) (mono f) c pre

  iterEndo-mono-chain-infl
    : (f : Endo)
    → (infl : ∀ c → _⊑_ c (fn f c))
    → ∀ n → _⊑_ (iterEndo f n) (iterEndo f (suc n))
  iterEndo-mono-chain-infl f infl =
    iter-mono-chain-infl (fn f) infl

  muEndo-unfold-right
    : (f : Endo)
    → ScottContinuous (fn f)
    → (mono-chain : ∀ n → _⊑_ (iterEndo f n) (iterEndo f (suc n)))
    → _⊑_ (fn f (muEndo f)) (muEndo f)
  muEndo-unfold-right f SC mono-chain =
    μF-unfold-right (fn f) SC mono-chain

  muEndo-unfold-right-infl
    : (f : Endo)
    → ScottContinuous (fn f)
    → (infl : ∀ c → _⊑_ c (fn f c))
    → _⊑_ (fn f (muEndo f)) (muEndo f)
  muEndo-unfold-right-infl f SC infl =
    μF-unfold-right-infl (fn f) SC infl
