{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Presentation dependence, made explicit (systems-engineering reading).
--
-- A view fixes an observation interface into a semantic target preorder.
-- Many internal “implementations” (rewrite relations, simulations, optimisations,
-- proof systems, ...) can be layered behind the same observation interface.
--
-- The only admissible criterion for comparing those implementations is
-- respect for explicit observation:
-- - observation-respecting means the chosen presentation preorder is monotone w.r.t. the view.
--
-- The canonical refinement is always the pullback refinement along the view.
-- Any observation-respecting presentation refines into it.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; MonoMap)
private
  module CPReasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.View using (View; μ; PullbackPreorder; _⊑[_]_)
open import LogOS.Syntax.Prop using (_↔_; intro)

-- --------------------------------------------------------------------------
-- Presentations: any preorder respecting a view.

record Presentation
  {ℓX ℓR ℓOCon ℓORel : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓOCon ℓORel}
  (V : View X O)
  : Set (lsuc (ℓX ⊔ ℓR ⊔ ℓOCon ⊔ ℓORel)) where
  infix 4 _≼_
  field
    _≼_        : X → X → Set ℓR
    refl≼      : ∀ {x} → x ≼ x
    trans≼     : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
    observe-mono
      : ∀ {x y} → x ≼ y → x ⊑[ V ] y

  CP : ConPreorder ℓX ℓR
  CP =
    record
      { Con   = X
      ; _⊑_   = _≼_
      ; refl  = refl≼
      ; trans = trans≼
      }

  -- Any observation-respecting presentation refines into the canonical pullback refinement.
  toCanonical : MonoMap CP (PullbackPreorder V) (λ x → x)
  toCanonical le = observe-mono le

-- Preorder reasoning combinators for a presentation relation `_≼_`.
--
-- This is a thin wrapper around `ConPreorder.Reasoning` on `Presentation.CP`,
-- but with names that read like presentation-refinement chains:
--
--   begin≼
--     a ≼⟨ ab ⟩
--     b ≼⟨ bc ⟩
--     c ∎≼
module PresentationReasoning
  {ℓX ℓR ℓOCon ℓORel : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓOCon ℓORel}
  {V : View X O}
  (P : Presentation {ℓR = ℓR} V)
  where

  private
    CP : ConPreorder ℓX ℓR
    CP = Presentation.CP P

  infix  1 begin≼_
  infixr 2 _≼⟨_⟩_
  infix  3 _∎≼

  module R = CPReasoning CP

  begin≼_ : ∀ {a b : X} → Presentation._≼_ P a b → Presentation._≼_ P a b
  begin≼_ = R.begin⊑_

  _≼⟨_⟩_
    : ∀ a {b c : X}
    → Presentation._≼_ P a b
    → Presentation._≼_ P b c
    → Presentation._≼_ P a c
  _≼⟨_⟩_ = R._⊑⟨_⟩_

  _∎≼ : ∀ a → Presentation._≼_ P a a
  _∎≼ = R._∎⊑

-- --------------------------------------------------------------------------
-- Canonical presentation + completeness.

-- The canonical presentation induced by a view: take the pullback refinement
-- itself as the implementation relation.
canonicalPresentation
  : ∀ {ℓX ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
  → (V : View X O)
  → Presentation {ℓR = ℓORel} V
canonicalPresentation {O = O} V =
  record
    { _≼_ = λ x y → x ⊑[ V ] y
    ; refl≼ = ConPreorder.refl O
    ; trans≼ = λ {x} {y} {z} xy yz →
        let
          module R = CPReasoning O
        in
        R._⊑⟨_⟩_ (μ V x) xy yz
    ; observe-mono = λ le → le
    }

-- Completeness of a presentation: semantic refinement along the view implies
-- derivability in the chosen presentation preorder.
record CompletePresentation
  {ℓX ℓR ℓOCon ℓORel : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓOCon ℓORel}
  {V : View X O}
  (P : Presentation {ℓR = ℓR} V)
  : Set (lsuc (ℓX ⊔ ℓR ⊔ ℓOCon ⊔ ℓORel)) where
  field
    fromCanonical : ∀ {x y} → x ⊑[ V ] y → Presentation._≼_ P x y

open CompletePresentation public
-- Soundness + completeness yields equivalence with the canonical pullback refinement.
presentation↔canonical
  : ∀ {ℓX ℓR ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    {V : View X O}
    (P : Presentation {ℓR = ℓR} V)
  → CompletePresentation P
  → ∀ {x y}
  → (Presentation._≼_ P x y) ↔ (x ⊑[ V ] y)
presentation↔canonical P C =
  intro
    (Presentation.observe-mono P)
    (fromCanonical C)

-- Canonical presentations are complete by construction.
canonicalComplete
  : ∀ {ℓX ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    (V : View X O)
  → CompletePresentation (canonicalPresentation V)
canonicalComplete V =
  record { fromCanonical = λ le → le }
