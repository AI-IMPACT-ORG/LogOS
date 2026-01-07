{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetU.GraphTreeBridge where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Domain.ZFC.SetU.WFGraphCore as Core

-- This module adds the *extra structure* needed to fold trees back into the
-- graph carrier, but keeps it explicit as an assumption record.
--
-- Think of `Sup` as “set formation” on the graph carrier.
-- (No category words: this is exactly the algebra structure for the tree functor.)

record SupStructure {ℓ : Level} (G : Core.WFGraph ℓ) : Set (lsuc ℓ) where
  open Core.WFGraph G renaming (Node to N; Edge to E)
  field
    supN : (I : Set ℓ) → (I → N) → N

    -- Membership of a sup-node is exactly membership in its generating family.
    mem-sup↔
      : ∀ {I : Set ℓ} {f : I → N} {y : N}
      → E (supN I f) y ↔ (Σ I (λ i → f i ≡ y))

open SupStructure public

module _ {ℓ : Level} {G : Core.WFGraph ℓ} (S : SupStructure G) where
  open Core.WFGraph G renaming (Node to N; Edge to E)
  open SupStructure S renaming (supN to supNₛ; mem-sup↔ to mem-sup↔ₛ)

  -- Fold any tree back into the graph carrier using the supplied `supN`.
  fold : Core.Tree N → N
  fold (Core.sup _ I kids) = supNₛ I (λ i → fold (kids i))

  -- Basic soundness: every direct child subtree folds to a member.
  fold-child→edge
    : ∀ {x : N} {I : Set ℓ} {kids : I → Core.Tree N} {i : I}
    → E (fold (Core.sup x I kids)) (fold (kids i))
  fold-child→edge {x} {I} {kids} {i} =
    _↔_.from (mem-sup↔ₛ {I = I} {f = λ j → fold (kids j)} {y = fold (kids i)})
      (i , refl)
