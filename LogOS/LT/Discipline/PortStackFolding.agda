{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Discipline.PortStackFolding where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Port-stack discipline gates.
--
-- This module is intentionally brittle: it asserts that port stacking is
-- definitionally implemented as a right-associated displayed product, and that
-- the canonical forgetful functors compute to the standard product projections
-- in the base cases.

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
open import LogOS.LT.Ports.PortStack.Raw using
  ( PortStack
  ; [_]
  ; _∷⁺_
  ; StackDisplayed
  ; forgetStack
  ; mkMemberStack
  ; hereEntry
  ; thereEntry
  ; forgetToPort
  ; Substack
  ; last
  ; drop
  ; forgetSubstack
  )

import LogOS.LT.Ports.PortSig as PortSig

private
  StackDisplayed-step-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      (p : PortSig.PortEntry C)
      (ps : PortStack C)
    → StackDisplayed (p ∷⁺ ps)
      ≡ ProductDisplayed (PortSig.Displayed (PortSig.sig p)) (StackDisplayed ps)
  StackDisplayed-step-def _ _ = refl

  forgetStack-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      (S : PortStack C)
    → forgetStack S
      ≡ forgetDecorated (StackDisplayed S)
  forgetStack-def _ = refl

  forgetToPort-singleton-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label : PortSig.PortLabel}
      {ℓTag : Level} {Tag : Set ℓTag}
      (sig₁ : PortSig C label Tag)
    → forgetToPort {S = [ mkPortEntry label ℓTag Tag sig₁ ]} (mkMemberStack hereEntry)
      ≡ idThin2Functor (DecoratedThin2Cat (StackDisplayed [ mkPortEntry label ℓTag Tag sig₁ ]))
  forgetToPort-singleton-def _ = refl

  forgetToPort-head-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label : PortSig.PortLabel}
      {ℓTag : Level} {Tag : Set ℓTag}
      (sig₁ : PortSig C label Tag)
      (ps : PortStack C)
    → forgetToPort {S = mkPortEntry label ℓTag Tag sig₁ ∷⁺ ps} (mkMemberStack hereEntry)
      ≡
        forgetProductLeft
          (PortSig.Displayed sig₁)
          (StackDisplayed ps)
  forgetToPort-head-def _ _ = refl

  forgetToPort-right2-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label₁ label₂ : PortSig.PortLabel}
      {ℓTag₁ : Level} {Tag₁ : Set ℓTag₁}
      {ℓTag₂ : Level} {Tag₂ : Set ℓTag₂}
      (sig₁ : PortSig C label₁ Tag₁)
      (sig₂ : PortSig C label₂ Tag₂)
    → forgetToPort
        {S = mkPortEntry label₁ ℓTag₁ Tag₁ sig₁ ∷⁺ [ mkPortEntry label₂ ℓTag₂ Tag₂ sig₂ ]}
        (mkMemberStack (thereEntry hereEntry))
      ≡
        forgetProductRight
          (PortSig.Displayed sig₁)
          (PortSig.Displayed sig₂)
  forgetToPort-right2-def _ _ = refl

  forgetSubstack-dropLast2-def
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {label₁ label₂ : PortSig.PortLabel}
      {ℓTag₁ : Level} {Tag₁ : Set ℓTag₁}
      {ℓTag₂ : Level} {Tag₂ : Set ℓTag₂}
      (sig₁ : PortSig C label₁ Tag₁)
      (sig₂ : PortSig C label₂ Tag₂)
    → forgetSubstack
        {Y = [ mkPortEntry label₂ ℓTag₂ Tag₂ sig₂ ]}
        {X = mkPortEntry label₁ ℓTag₁ Tag₁ sig₁ ∷⁺ [ mkPortEntry label₂ ℓTag₂ Tag₂ sig₂ ]}
        (drop last)
      ≡
        forgetProductRight
          (PortSig.Displayed sig₁)
          (PortSig.Displayed sig₂)
  forgetSubstack-dropLast2-def _ _ = refl

-- Export one harmless witness so this module can be imported via the API
-- without re-exporting all internal discipline lemmas.
ok : ⊤ {ℓ = lzero}
ok = tt
