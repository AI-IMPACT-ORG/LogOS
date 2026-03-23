{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PreQuantum.Discard2Cat where

-- The thin 2-category of objects equipped with explicit discard morphisms.
--
-- Objects: a base object `A` together with a chosen “discard” morphism
--   `dA : A → I` into the monoidal unit.
--
-- Morphisms: base morphisms that preserve the chosen discards up to observation:
--   `dB ∘ f ≈ dA`.
--
-- This is a Σ-decoration of a displayed structure over the base category.
--
-- Note: this is strictly *more general* than `DiscardStructure`:
-- a global discard structure determines a canonical section into this category,
-- but this category also supports non-canonical (per-object) discard choices.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.ConPreorder using (Con; _⊑_; _≈_)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

open import LogOS.Ports.PreQuantum.Monoidal using (SymmetricMonoidalData)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data DiscardTag : Set where
  discardTag : DiscardTag

discardTagId : ℕ
discardTagId = 16

module Discard2CatLocal
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (CL : Thin2CatLaws C)
  (M : SymmetricMonoidalData C)
  where

  open Thin2Cat C
  open Thin2CatLaws CL
  private
    I : Obj
    I = SymmetricMonoidalData.I M

  DiscardPort : Obj → Set ℓHomCon
  DiscardPort A = Con (Hom A I)

  DiscardLaw
    : ∀ {A B}
    → Con (Hom A B)
    → DiscardPort A
    → DiscardPort B
    → Set ℓHomRel
  DiscardLaw {A} {B} f dA dB = _≈_ (Hom A I) (dB ∘ f) dA

  idDiscardLaw : ∀ {A} (dA : DiscardPort A) → DiscardLaw (id {A}) dA dA
  idDiscardLaw dA = id-right dA

  compDiscardLaw
    : ∀ {A B D}
      {f : Con (Hom A B)}
      {g : Con (Hom B D)}
      {dA : DiscardPort A}
      {dB : DiscardPort B}
      {dD : DiscardPort D}
    → DiscardLaw f dA dB
    → DiscardLaw g dB dD
    → DiscardLaw (g ∘ f) dA dD
  compDiscardLaw {A} {B} {f = f} {g = g} {dA = dA} {dB = dB} {dD = dD} p q =
    ( r₁ , r₂ )
    where
      module R = ≤-Reasoning (Hom A I)
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)

      p₁ : _⊑_ (Hom A I) (dB ∘ f) dA
      p₁ = fst p

      p₂ : _⊑_ (Hom A I) dA (dB ∘ f)
      p₂ = snd p

      q₁ : _⊑_ (Hom B I) (dD ∘ g) dB
      q₁ = fst q

      q₂ : _⊑_ (Hom B I) dB (dD ∘ g)
      q₂ = snd q

      r₁ : _⊑_ (Hom A I) (dD ∘ (g ∘ f)) dA
      r₁ =
        begin⊑
          (dD ∘ (g ∘ f))
            ⊑⟨ snd (assoc dD g f) ⟩
          ((dD ∘ g) ∘ f)
            ⊑⟨ comp-mono-l q₁ ⟩
          (dB ∘ f)
            ⊑⟨ p₁ ⟩
          dA ∎⊑

      r₂ : _⊑_ (Hom A I) dA (dD ∘ (g ∘ f))
      r₂ =
        begin⊑
          dA
            ⊑⟨ p₂ ⟩
          (dB ∘ f)
            ⊑⟨ comp-mono-l q₂ ⟩
          ((dD ∘ g) ∘ f)
            ⊑⟨ fst (assoc dD g f) ⟩
          (dD ∘ (g ∘ f)) ∎⊑

  DiscardDisplayed : DisplayedThin2Cat C ℓHomCon ℓHomRel
  DiscardDisplayed =
    record
      { Ob = DiscardPort
      ; HomD = λ {A} {B} (f : Con (Hom A B)) dA dB → DiscardLaw f dA dB
      ; idD = idDiscardLaw
      ; compD = λ p q → compDiscardLaw p q
      }

  module Port
    = Template.SingletonLayer
        discardTagId
        {Tag = DiscardTag}
        DiscardDisplayed

  discardSig : PortSig.PortSig C discardTagId DiscardTag
  discardSig = Port.portSig

  open Port public using
    ( port2Cat
    ; singleton
    ; stack
    ; port
    ; Displayed
    ; WithPort
    ; forget
    )

open Discard2CatLocal public using
  ( DiscardDisplayed
  ; discardSig
  ; port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  )
