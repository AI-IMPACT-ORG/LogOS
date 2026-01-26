{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetU.WFGraphCore where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)

-- Minimal well-founded graph carrier + its unfolding into a W-style tree view.
--
-- This is deliberately foundational and axiom-free:
-- it does not commit to a particular extensional equality, normal form, or
-- quotienting discipline. Those are supplied by downstream “kernel laws”.

-- Accessibility / well-foundedness (defined locally, to avoid extra dependencies).

data Acc {ℓ : Level} {A : Set ℓ} (R : A → A → Set ℓ) (x : A) : Set (lsuc ℓ) where
  acc : (∀ y → R y x → Acc R y) → Acc R x

-- A well-founded membership graph: `Edge x y` means “y is an element of x”.

record WFGraph (ℓ : Level) : Set (lsuc ℓ) where
  field
    Node : Set ℓ
    Edge : Node → Node → Set ℓ

    -- Well-foundedness of membership: every node is accessible via its members.
    wf   : (x : Node) → Acc (λ y x → Edge x y) x

open WFGraph public

-- Tree view: a node labelled by its root, with children indexed by some set `I`.
-- For `unfold`, the index set is the Σ-type of outgoing edges.

data Tree {ℓ : Level} (N : Set ℓ) : Set (lsuc ℓ) where
  sup : (root : N) (I : Set ℓ) (kids : I → Tree N) → Tree N

root : ∀ {ℓ} {N : Set ℓ} → Tree N → N
root (sup x _ _) = x

-- “Immediate child node”: y occurs as the root of a direct child subtree.

ChildNode : ∀ {ℓ} {N : Set ℓ} → Tree N → N → Set ℓ
ChildNode (sup _ I kids) y = Σ I (λ i → root (kids i) ≡ y)

module _ {ℓ : Level} (G : WFGraph ℓ) where
  private
    N : Set ℓ
    N = WFGraph.Node G

    E : N → N → Set ℓ
    E = WFGraph.Edge G

    wfN : (x : N) → Acc (λ y x → E x y) x
    wfN = WFGraph.wf G

  -- Unfold a node into its membership tree using `wf`.
  --
  -- Children are indexed by outgoing edges from the current root:
  -- `I x = Σ y. Edge x y`, and the `i`-th child is `unfold y`.

  unfoldAcc : ∀ {x} → Acc (λ y x → E x y) x → Tree N
  unfoldAcc {x} (acc step) =
    sup x (Σ N (λ y → E x y))
      (λ { (y , e) → unfoldAcc (step y e) })

  unfold : N → Tree N
  unfold x = unfoldAcc {x = x} (wfN x)

  root-unfoldAcc : ∀ {x} (a : Acc (λ y x → E x y) x) → root (unfoldAcc {x = x} a) ≡ x
  root-unfoldAcc (acc _) = refl

  root-unfold : ∀ x → root (unfold x) ≡ x
  root-unfold x = root-unfoldAcc (wfN x)

  edge→child
    : ∀ {x y}
    → E x y
    → ChildNode (unfold x) y
  edge→child {x} {y} e with wfN x
  ... | acc step =
    (y , e) , root-unfoldAcc (step y e)

  child→edge
    : ∀ {x y}
    → ChildNode (unfold x) y
    → E x y
  child→edge {x} {y} cn with wfN x
  ... | acc step with cn
  ...   | (i , pr) with i
  ...     | (y' , e) =
        let y'≡y = trans (sym (root-unfoldAcc (step y' e))) pr
        in subst (λ t → E x t) y'≡y e
