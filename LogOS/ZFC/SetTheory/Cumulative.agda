{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.Cumulative where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; intro)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.API.Kernel
open import LogOS.API.Kernel.TensorDSL
open import LogOS.API.Kernel.Eq using (module ForKernel)

open import LogOS.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)

record StageIndex : Set₁ where
  infix 4 _≤_
  field
    I      : Set
    _≤_    : I → I → Set
    isSucc : I → Set
    isLim  : I → Set
    zeroStage   : I
    zero-isSucc : isSucc zeroStage
    join   : ∀ i j → Σ I (λ k → (_≤_ i k) × (_≤_ j k))
    succAbove : ∀ i → Σ I (λ k → isSucc k × (_≤_ i k))

record StageSet {ℓU : Level} (S : StageIndex) : Set (lsuc ℓU) where
  open StageIndex S
  infix 4 _∈ᵢ_ _≈ᵢ_
  field
    U      : I → Set ℓU
    _∈ᵢ_   : ∀ {i} → U i → U i → Set ℓU
    _≈ᵢ_   : ∀ {i} → U i → U i → Set ℓU
    refl≈ᵢ  : ∀ {i} x → _≈ᵢ_ {i} x x
    sym≈ᵢ   : ∀ {i} {x y} → _≈ᵢ_ {i} x y → _≈ᵢ_ {i} y x
    trans≈ᵢ : ∀ {i} {x y z} → _≈ᵢ_ {i} x y → _≈ᵢ_ {i} y z → _≈ᵢ_ {i} x z
    extensionalityᵢ : ∀ {i} x y → (∀ z → (z ∈ᵢ x) ↔ (z ∈ᵢ y)) → _≈ᵢ_ {i} x y
    mem-extᵢ        : ∀ {i} {x y} → _≈ᵢ_ {i} x y → ∀ z → (z ∈ᵢ x) ↔ (z ∈ᵢ y)
    emb    : ∀ {i j} → _≤_ i j → U i → U j
    emb-∈  : ∀ {i j} (p : _≤_ i j) {x y} → _∈ᵢ_ {i} x y → _∈ᵢ_ {j} (emb p x) (emb p y)
    emb-≈  : ∀ {i j} (p : _≤_ i j) {x y} → _≈ᵢ_ {i} x y → _≈ᵢ_ {j} (emb p x) (emb p y)

record SuccessorClosure {ℓU : Level} (S : StageIndex) (SS : StageSet {ℓU} S) : Set (lsuc ℓU) where
  open StageIndex S; open StageSet SS
  field
    emptyᵢ    : ∀ {i} → isSucc i → Σ (U i) (λ e → ∀ z → ¬ (z ∈ᵢ e))
    pairingᵢ  : ∀ {i} → isSucc i → ∀ x y → Σ (U i) (λ p → ∀ z → (z ∈ᵢ p) ↔ ((z ≈ᵢ x) ⊎ (z ≈ᵢ y)))
    unionᵢ    : ∀ {i} → isSucc i → ∀ x → Σ (U i) (λ u → ∀ z → (z ∈ᵢ u) ↔ (Σ (U i) (λ y → (y ∈ᵢ x) × (z ∈ᵢ y))))
    powersetᵢ : ∀ {i} → isSucc i → ∀ x → Σ (U i) (λ p → ∀ z → (z ∈ᵢ p) ↔ (∀ w → w ∈ᵢ z → w ∈ᵢ x))

record LimitClosure {ℓU : Level} (S : StageIndex) (SS : StageSet {ℓU} S) : Set (lsuc ℓU) where
  open StageIndex S; open StageSet SS
  field
    unionLim : ∀ {i} → isLim i → (U i ≡ Σ I (λ j → Σ (_≤_ j i) (λ _ → U j)))

record RankBounding {ℓU : Level} (S : StageIndex) (SS : StageSet {ℓU} S) : Set (lsuc ℓU) where
  open StageIndex S; open StageSet SS
  field
    separationᵢ
      : ∀ {i} (P : U i → Set ℓU) (x : U i)
      → Σ (Σ I (λ j → _≤_ i j)) λ ij →
        Σ (U (proj₁ ij)) λ y →
          (z : U i) →
            (emb (proj₂ ij) z ∈ᵢ y)
              ↔ ((emb (proj₂ ij) z ∈ᵢ emb (proj₂ ij) x) × P z)
    replacementᵢ
      : ∀ {i} (F : U i → Σ (U i) (λ _ → Set ℓU)) (x : U i)
      → Σ (Σ I (λ j → _≤_ i j)) λ ij →
        Σ (U (proj₁ ij)) λ y →
          (z : U i) →
            (emb (proj₂ ij) z ∈ᵢ y)
              ↔ (Σ (U i) (λ u →
                      u ∈ᵢ x × (emb (proj₂ ij) (proj₁ (F u)) ≈ᵢ emb (proj₂ ij) z)))

-- Code extensionality helper: interpret `Code` into some carrier `U∞` in a way
-- that depends only on the decoded boundary constraint.
--
-- This is useful for “prototype” set-theory surfaces that must not depend on
-- intensional code representatives.
record DecodeBridge {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                    (K : Kernel Sig Q) (U∞ : Set)
                    : Set (lsuc ℓ) where
  open Kernel K
  open ForKernel K
  field
    ⟦_⟧       : Code → U∞
    by-decode≈ : ∀ {γ δ} → γ ≃K δ → ⟦ γ ⟧ ≡ ⟦ δ ⟧

-- Canonical builder: any map out of boundary constraints yields a DecodeBridge by
-- composing with `decode`.
mkDecodeBridge
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) {U∞ : Set}
    (f : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K)) → U∞)
  → DecodeBridge K U∞
mkDecodeBridge K f = record
  { ⟦_⟧       = λ γ → f (Kernel.decode K γ)
  ; by-decode≈ = cong f
  }

record StageToCH {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  private
    module Bnd = ConPreorder (BulkBoundary.bnd BB)
  field
    S   : StageIndex
    SS  : StageSet {ℓ} S
    SC  : SuccessorClosure {ℓ} S SS
    LC  : LimitClosure {ℓ} S SS
    RB  : RankBounding {ℓ} S SS
    CH  : CumulativeHierarchy K

    realise∞       : CumulativeHierarchy.SetU CH → Bnd.Con
    mem⇒flow∞      : ∀ {x y} → CumulativeHierarchy._∈_ CH x y
                   → Bnd._⊑_ (realise∞ x) (Endo.fn (Flow-Endo K) (realise∞ y))
    eq⇒realise∞≡   : ∀ {x y} → CumulativeHierarchy._≈_ CH x y → realise∞ x ≡ realise∞ y
    tf-stable∞     : ∀ x → Bnd._⊑_ (Endo.fn (Flow-Endo K) (realise∞ x)) (realise∞ x)
