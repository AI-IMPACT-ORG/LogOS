{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Soundness.Logic where

open import LogOS.Prelude using
  ( Level
  ; _×_
  ; _⊎_
  ; Σ
  ; _,_
  ; fst
  ; snd
  ; inj₁
  ; inj₂
  ; refl
  ; sym
  ; trans
  ; cong
  ; cong₂
  ; subst
  ; ⊥-elim
  ; _≡_
  ; ℕ
  ; zero
  )

open import LogOS.Syntax.Prop using (_↔_; intro; to; from)

import LogOS.Apps.ZFC.Proof.Syntax as Syntax
open Syntax
import LogOS.Apps.ZFC.Proof.Axioms as Ax
open Ax

import LogOS.Apps.ZFC.Proof.Semantics.Core as Core

module ForModel {ℓ : Level} (M : Core.Model {ℓ}) where
  open Core.Model M
  private
    module MC = Core.ModelCore M

  open MC using
    ( evalFormula-cong
    ; insertAt-zero-extend
    ; evalFormula-lift
    ; evalFormula-substAt
    )

  logicEqSound : ∀ {ρ φ} → LogicEqAxiom φ → evalFormula φ ρ
  logicEqSound (axK φ ψ) = λ p q → p
  logicEqSound (axS φ ψ χ) = λ f g h → f h (g h)
  logicEqSound (axBottom φ) = λ ()

  logicEqSound (axAndIntro φ ψ) = λ p q → (p , q)
  logicEqSound (axAndElimL φ ψ) = fst
  logicEqSound (axAndElimR φ ψ) = snd

  logicEqSound (axOrIntroL φ ψ) = inj₁
  logicEqSound (axOrIntroR φ ψ) = inj₂
  logicEqSound (axOrElim φ ψ χ) =
    λ f g → λ where
      (inj₁ p) → f p
      (inj₂ q) → g q

  logicEqSound (axIffIntro φ ψ) = λ f g → intro f g
  logicEqSound (axIffElimL φ ψ) = λ p x → to p x
  logicEqSound (axIffElimR φ ψ) = λ p y → from p y
  logicEqSound {ρ} (axAllElim φ t) =
    λ allφ →
      from
        (evalFormula-substAt zero t φ ρ)
        (from
          (evalFormula-cong (insertAt-zero-extend (evalTerm t ρ) ρ) φ)
          (allφ (evalTerm t ρ)))
  logicEqSound (axAllImp φ ψ) =
    λ f g x → f x (g x)
  logicEqSound {ρ} (axAllIntro A φ) =
    λ allImp a x →
      (allImp x) (from (evalFormula-lift A ρ x) a)

  logicEqSound {ρ} (axExIntro φ t) =
    λ h →
      evalTerm t ρ
      , to
          (evalFormula-cong (insertAt-zero-extend (evalTerm t ρ) ρ) φ)
          (to (evalFormula-substAt zero t φ ρ) h)
  logicEqSound {ρ} (axExElim φ A) =
    λ allImp → λ where
      (x , px) →
        to (evalFormula-lift A ρ x) ((allImp x) px)

  logicEqSound (axEqSym t u) = sym≈
  logicEqSound (axEqTrans t u v) = λ tu uv → trans≈ tu uv
  logicEqSound {ρ} (axMemExt t u v) eq =
    mem-ext eq (evalTerm t ρ)
  logicEqSound {ρ} (axEqRefl t) = refl≈ (evalTerm t ρ)

  -- Optional extensionality strengthening: canonical representatives.
  --
  -- If `≈` implies propositional equality on the semantic carrier, then `≈F`
  -- behaves like standard first-order equality (substitutive/congruent).

  Extensionality : Set ℓ
  Extensionality = ∀ {x y : SetU} → x ≈ y → x ≡ y

  -- A slightly more “semantic” strengthening: membership extensionality implies
  -- propositional equality.
  --
  -- This matches canonical-representative/quotient-style assumptions (e.g. a
  -- canonical-representatives / extensional-quotient ledger item) and can be specialised to `Extensionality`
  -- using `mem-ext`.

  ExtensionalityByMembers : Set ℓ
  ExtensionalityByMembers =
    ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≡ y

  extensionalityFromMembers : ExtensionalityByMembers → Extensionality
  extensionalityFromMembers ext≡ {x} {y} xy =
    ext≡ x y (mem-ext xy)

  logicEqExtSound
    : ∀ {ρ φ}
    → Extensionality
    → LogicEqAxiomExt φ
    → evalFormula φ ρ
  logicEqExtSound ext (axBase l) = logicEqSound l
  logicEqExtSound {ρ} ext (axMemCongL t u v) tu =
    let
      eq : evalTerm t ρ ≡ evalTerm u ρ
      eq = ext tu
    in
    intro
      (λ tv → subst (λ z → z ∈ evalTerm v ρ) eq tv)
      (λ uv → subst (λ z → z ∈ evalTerm v ρ) (sym eq) uv)
  logicEqExtSound {ρ} ext (axPairCongL t u v) tu =
    ≡→≈ (cong₂ pairSet (ext tu) refl)
  logicEqExtSound {ρ} ext (axPairCongR t u v) tu =
    ≡→≈ (cong₂ pairSet refl (ext tu))
  logicEqExtSound {ρ} ext (axUnionCong t u) tu =
    ≡→≈ (cong unionSet (ext tu))
  logicEqExtSound {ρ} ext (axPowerCong t u) tu =
    ≡→≈ (cong powersetSet (ext tu))
  logicEqExtSound {ρ} ext (axSuccCong t u) tu =
    ≡→≈ (cong succSet (ext tu))

  extensionality≈ : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
  extensionality≈ x y hyp =
    ( (λ z exz → to (hyp z) exz)
    , (λ z eyz → from (hyp z) eyz)
    )
