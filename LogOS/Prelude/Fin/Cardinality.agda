{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.Fin.Cardinality where

-- Constructive finite-cardinality lemmas for explicit `Fin`-indexed families.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.Fin using
  ( Fin
  ; fzero
  ; fsuc
  ; _≢_
  ; finEq
  ; lowerFromDiff
  ; lowerFromDiff-cong
  ; lowerFromDiff-raiseExcept
  ; raiseExcept
  ; raiseExcept-≢
  )
open import LogOS.Prelude.Nat.Order using (_≤ℕ_; z≤n; s≤s)

private
  findWitness
    : ∀ {n m}
    → (assign : Fin n → Fin m)
    → (j : Fin m)
    → (Σ (Fin n) (λ i → assign i ≡ j))
       ⊎
       ((i : Fin n) → assign i ≢ j)
  findWitness {zero} assign j = inj₂ (λ ())
  findWitness {suc n} assign j with finEq (assign fzero) j
  ... | inj₁ eq = inj₁ (fzero , eq)
  ... | inj₂ neq with findWitness (λ i → assign (fsuc i)) j
  ... | inj₁ (i , eq) = inj₁ (fsuc i , eq)
  ... | inj₂ none =
      inj₂
        (λ where
          fzero eq → neq eq
          (fsuc i) eq → none i eq)

  tailWitness
    : ∀ {n m}
    → (assign : Fin (suc n) → Fin m)
    → (j : Fin m)
    → (Σ (Fin n) (λ i → assign (fsuc i) ≡ j))
       ⊎
       ((i : Fin n) → assign (fsuc i) ≢ j)
  tailWitness assign j = findWitness (λ i → assign (fsuc i)) j

  ≤ℕ-suc-right : ∀ {m n} → m ≤ℕ n → m ≤ℕ suc n
  ≤ℕ-suc-right z≤n = z≤n
  ≤ℕ-suc-right (s≤s p) = s≤s (≤ℕ-suc-right p)

mutual
  surjective⇒size≤
    : ∀ {m n}
    → (assign : Fin n → Fin m)
    → (∀ j → Σ (Fin n) (λ i → assign i ≡ j))
    → m ≤ℕ n
  surjective⇒size≤ {m = zero} assign surjective = z≤n
  surjective⇒size≤ {m = suc m} {n = zero} assign surjective with surjective fzero
  ... | ()
  surjective⇒size≤ {m = suc m} {n = suc n} assign surjective
    with tailWitness assign (assign fzero)
  ... | inj₁ (dup , dupEq) =
      ≤ℕ-suc-right (surjective⇒size≤ tailAssign tailSurjective)
    where
      tailAssign : Fin n → Fin (suc m)
      tailAssign i = assign (fsuc i)

      tailSurjective
        : ∀ j
        → Σ (Fin n) (λ i → tailAssign i ≡ j)
      tailSurjective j with surjective j
      ... | fzero , eq = dup , trans dupEq eq
      ... | fsuc i , eq = i , eq
  ... | inj₂ noDup =
      s≤s (surjective⇒size≤ reducedAssign reducedSurjective)
    where
      j₀ : Fin (suc m)
      j₀ = assign fzero

      reducedAssign : Fin n → Fin m
      reducedAssign i = lowerFromDiff j₀ (assign (fsuc i)) (noDup i)

      reducedSurjective
        : ∀ k
        → Σ (Fin n) (λ i → reducedAssign i ≡ k)
      reducedSurjective k = fromRaised (surjective (raiseExcept j₀ k))
        where
          fromRaised
            : Σ (Fin (suc n)) (λ i → assign i ≡ raiseExcept j₀ k)
            → Σ (Fin n) (λ i → reducedAssign i ≡ k)
          fromRaised (fzero , eq) with raiseExcept-≢ j₀ k (sym eq)
          ... | ()
          fromRaised (fsuc i , eq) =
              i
            , trans
                (lowerFromDiff-cong j₀ eq (noDup i) (raiseExcept-≢ j₀ k))
                (lowerFromDiff-raiseExcept j₀ k)

  surjective+collision⇒suc-target≤source
    : ∀ {m n}
    → (assign : Fin n → Fin m)
    → (∀ j → Σ (Fin n) (λ i → assign i ≡ j))
    → (Σ (Fin n × Fin n) (λ { (i , k) → i ≢ k × assign i ≡ assign k }))
    → suc m ≤ℕ n
  surjective+collision⇒suc-target≤source {m = zero} assign surjective collision
    with fst (proj₁ collision)
  ... | i with assign i
  ... | ()
  surjective+collision⇒suc-target≤source {m = suc m} {n = zero} assign surjective collision
    with fst (proj₁ collision)
  ... | ()
  surjective+collision⇒suc-target≤source {m = suc m} {n = suc n} assign surjective collision
    with tailWitness assign (assign fzero)
  ... | inj₁ (dup , dupEq) =
      s≤s (surjective⇒size≤ tailAssign tailSurjective)
    where
      tailAssign : Fin n → Fin (suc m)
      tailAssign i = assign (fsuc i)

      tailSurjective
        : ∀ j
        → Σ (Fin n) (λ i → tailAssign i ≡ j)
      tailSurjective j with surjective j
      ... | fzero , eq = dup , trans dupEq eq
      ... | fsuc i , eq = i , eq
  ... | inj₂ noDup =
      s≤s
        (surjective+collision⇒suc-target≤source
          reducedAssign
          reducedSurjective
          reducedCollision)
    where
      j₀ : Fin (suc m)
      j₀ = assign fzero

      reducedAssign : Fin n → Fin m
      reducedAssign i = lowerFromDiff j₀ (assign (fsuc i)) (noDup i)

      reducedSurjective
        : ∀ k
        → Σ (Fin n) (λ i → reducedAssign i ≡ k)
      reducedSurjective k = fromRaised (surjective (raiseExcept j₀ k))
        where
          fromRaised
            : Σ (Fin (suc n)) (λ i → assign i ≡ raiseExcept j₀ k)
            → Σ (Fin n) (λ i → reducedAssign i ≡ k)
          fromRaised (fzero , eq) with raiseExcept-≢ j₀ k (sym eq)
          ... | ()
          fromRaised (fsuc i , eq) =
              i
            , trans
                (lowerFromDiff-cong j₀ eq (noDup i) (raiseExcept-≢ j₀ k))
                (lowerFromDiff-raiseExcept j₀ k)

      reducedCollision
        : Σ (Fin n × Fin n)
            (λ { (i , k) → i ≢ k × reducedAssign i ≡ reducedAssign k })
      reducedCollision = reduce collision
        where
          reduce
            : Σ (Fin (suc n) × Fin (suc n))
                (λ { (i , k) → i ≢ k × assign i ≡ assign k })
            → Σ (Fin n × Fin n)
                (λ { (i , k) → i ≢ k × reducedAssign i ≡ reducedAssign k })
          reduce ((fzero , fzero) , (distinct , merged)) with distinct refl
          ... | ()
          reduce ((fzero , fsuc k) , (distinct , merged)) with noDup k (sym merged)
          ... | ()
          reduce ((fsuc i , fzero) , (distinct , merged)) with noDup i merged
          ... | ()
          reduce ((fsuc i , fsuc k) , (distinct , merged)) =
              ( i , k )
            , ( (λ eq → distinct (cong fsuc eq))
              , lowerFromDiff-cong j₀ merged (noDup i) (noDup k)
              )

id-surjective⇒size≤
  : ∀ {n}
  → n ≤ℕ n
id-surjective⇒size≤ {n} =
  surjective⇒size≤ (λ (i : Fin n) → i) (λ j → j , refl)

collapseFin₂⇒Fin₁
  : suc (suc zero) ≤ℕ suc (suc zero)
collapseFin₂⇒Fin₁ =
  surjective+collision⇒suc-target≤source
    (λ _ → fzero)
    (λ { fzero → fzero , refl })
    ((fzero , fsuc fzero) , ((λ ()) , refl))
