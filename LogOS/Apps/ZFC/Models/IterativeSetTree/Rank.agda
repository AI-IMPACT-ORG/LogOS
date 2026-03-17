{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.Rank where

open import LogOS.Prelude

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST

-- Stage codes for the iterative-set-tree presentation.
--
-- We keep the stage language one universe above the raw tree indices so it can
-- serve directly as a stage preorder carrier for `ctxᵛ`.
data RankV {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  supʳ : (I : Set (lsuc ℓ)) → (I → RankV {ℓ}) → RankV {ℓ}

succʳ : ∀ {ℓ} → RankV {ℓ} → RankV {ℓ}
succʳ {ℓ} α = supʳ (Lift (lsuc ℓ) (Topℓ {ℓ})) (λ _ → α)

joinʳ : ∀ {ℓ} → RankV {ℓ} → RankV {ℓ} → RankV {ℓ}
joinʳ {ℓ} α β =
  supʳ
    (Lift (lsuc ℓ) (Topℓ {ℓ} ⊎ Topℓ {ℓ}))
    (λ where
      (lift (inj₁ _)) → α
      (lift (inj₂ _)) → β)

iterateSuccʳ : ∀ {ℓ} → ℕ → RankV {ℓ} → RankV {ℓ}
iterateSuccʳ zero α = α
iterateSuccʳ (suc n) α = succʳ (iterateSuccʳ n α)

infix 4 _≤ʳ_
data _≤ʳ_ {ℓ : Level} : RankV {ℓ} → RankV {ℓ} → Set (lsuc (lsuc ℓ)) where
  refl≤ʳ : ∀ {α} → α ≤ʳ α
  step≤ʳ
    : ∀ {α I r} (i : I)
    → α ≤ʳ r i
    → α ≤ʳ supʳ I r

≤ʳ-refl : ∀ {ℓ} {α : RankV {ℓ}} → α ≤ʳ α
≤ʳ-refl = refl≤ʳ

≤ʳ-trans
  : ∀ {ℓ} {α β γ : RankV {ℓ}}
  → α ≤ʳ β
  → β ≤ʳ γ
  → α ≤ʳ γ
≤ʳ-trans α≤β refl≤ʳ = α≤β
≤ʳ-trans α≤β (step≤ʳ i β≤child) = step≤ʳ i (≤ʳ-trans α≤β β≤child)

≤ʳ-succ : ∀ {ℓ} {α : RankV {ℓ}} → α ≤ʳ succʳ α
≤ʳ-succ {ℓ} = step≤ʳ (lift ttℓ) refl≤ʳ

≤ʳ-joinˡ : ∀ {ℓ} {α β : RankV {ℓ}} → α ≤ʳ joinʳ α β
≤ʳ-joinˡ {ℓ} = step≤ʳ (lift (inj₁ ttℓ)) refl≤ʳ

≤ʳ-joinʳ : ∀ {ℓ} {α β : RankV {ℓ}} → β ≤ʳ joinʳ α β
≤ʳ-joinʳ {ℓ} = step≤ʳ (lift (inj₂ ttℓ)) refl≤ʳ

rankᵛ : ∀ {ℓ} → IST.V {ℓ} → RankV {ℓ}
rankᵛ {ℓ} (IST.sup I f) =
  supʳ
    (Lift (lsuc ℓ) I)
    (λ where (lift i) → succʳ (rankᵛ (f i)))
