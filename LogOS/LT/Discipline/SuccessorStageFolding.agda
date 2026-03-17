{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Discipline.SuccessorStageFolding where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Successor-stage discipline gates.
--
-- This module is intentionally brittle: it asserts that the generic
-- successor-stage wrapper computes definitionally to the displayed/Σ-totalised
-- port template surfaces used elsewhere in LT.

open import LogOS.Prelude using (Level; lzero; ⊤; tt; _≡_; refl)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (idThin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( ProductDisplayed
  ; DecoratedThin2Cat
  ; forgetDecorated
  ; forgetProductLeft
  ; forgetProductRight
  )
open import LogOS.LT.Ports.PortSig using (PortSig; mkPortEntry)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.Template.Singleton2Cat as Singleton
import LogOS.LT.Ports.Template.Stack2Cat as Stack

private
  singletonDisplayed-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label : PortSig.PortLabel}
      {ℓTag : Level} {Tag : Set ℓTag}
      (sig : PortSig C label Tag)
    → Singleton.Displayed (Singleton.mkSingleton2Cat sig)
      ≡ PortSig.Displayed sig
  singletonDisplayed-def _ = refl

  singletonWithPort-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label : PortSig.PortLabel}
      {ℓTag : Level} {Tag : Set ℓTag}
      (sig : PortSig C label Tag)
    → Singleton.WithPort (Singleton.mkSingleton2Cat sig)
      ≡ DecoratedThin2Cat (PortSig.Displayed sig)
  singletonWithPort-def _ = refl

  singletonForget-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label : PortSig.PortLabel}
      {ℓTag : Level} {Tag : Set ℓTag}
      (sig : PortSig C label Tag)
    → Singleton.forget (Singleton.mkSingleton2Cat sig)
      ≡ forgetDecorated (PortSig.Displayed sig)
  singletonForget-def _ = refl

  stackDisplayed-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      (S : PortStack.PortStack C)
    → Stack.Displayed (Stack.mkStack2Cat S)
      ≡ PortStack.StackDisplayed S
  stackDisplayed-def _ = refl

  stackWithPort-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      (S : PortStack.PortStack C)
    → Stack.WithPort (Stack.mkStack2Cat S)
      ≡ DecoratedThin2Cat (PortStack.StackDisplayed S)
  stackWithPort-def _ = refl

  stackForget-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      (S : PortStack.PortStack C)
    → Stack.forget (Stack.mkStack2Cat S)
      ≡ forgetDecorated (PortStack.StackDisplayed S)
  stackForget-def _ = refl

  singletonForget-head-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label₁ label₂ : PortSig.PortLabel}
      {ℓTag₁ : Level} {Tag₁ : Set ℓTag₁}
      {ℓTag₂ : Level} {Tag₂ : Set ℓTag₂}
      (sig₁ : PortSig C label₁ Tag₁)
      (sig₂ : PortSig C label₂ Tag₂)
    → PortStack.forgetToPort
        {S =
          PortStack._∷⁺_
            (mkPortEntry label₁ ℓTag₁ Tag₁ sig₁)
            (PortStack.[ mkPortEntry label₂ ℓTag₂ Tag₂ sig₂ ])}
        (PortStack.mkMemberStack PortStack.hereEntry)
      ≡
        forgetProductLeft
          (PortSig.Displayed sig₁)
          (PortSig.Displayed sig₂)
  singletonForget-head-def _ _ = refl

  stackForget-right2-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label₁ label₂ : PortSig.PortLabel}
      {ℓTag₁ : Level} {Tag₁ : Set ℓTag₁}
      {ℓTag₂ : Level} {Tag₂ : Set ℓTag₂}
      (sig₁ : PortSig C label₁ Tag₁)
      (sig₂ : PortSig C label₂ Tag₂)
    → PortStack.forgetSubstack
        {Y = PortStack.[ mkPortEntry label₂ ℓTag₂ Tag₂ sig₂ ]}
        {X =
          PortStack._∷⁺_
            (mkPortEntry label₁ ℓTag₁ Tag₁ sig₁)
            (PortStack.[ mkPortEntry label₂ ℓTag₂ Tag₂ sig₂ ])}
        (PortStack.drop PortStack.last)
      ≡
        forgetProductRight
          (PortSig.Displayed sig₁)
          (PortSig.Displayed sig₂)
  stackForget-right2-def _ _ = refl

ok : ⊤ {ℓ = lzero}
ok = tt
