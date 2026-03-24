{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.PortLabelPayloadSplit where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using (LawDisplayedOn)
open import LogOS.LT.Ports.PortSig using (PortEntry; PortSig; mkEntry)
open import LogOS.LT.Ports.PortStack.Raw using
  ( Listω
  ; []
  ; _∷_
  ; NoDupStack
  ; [_]
  ; _∷⁺_
  ; EntryMember
  ; hereEntry
  ; thereEntry
  ; entryMember⇒member
  ; Member
  )
open import LogOS.LT.Ports.PortStack.Unique using (noDupSingleton; noDupCons)

data ⋆ : Set where
  tt⋆ : ⋆

onePreorder : ConPreorder lzero lzero
onePreorder =
  record
    { Con = ⋆
    ; _⊑_ = λ _ _ → ⊤
    ; refl = tt
    ; trans = λ _ _ → tt
    }

oneThin2Cat : Thin2Cat lzero lzero lzero
oneThin2Cat =
  record
    { Obj = ⋆
    ; Hom = λ _ _ → onePreorder
    ; id = tt⋆
    ; _∘_ = λ _ _ → tt⋆
    ; comp-mono-l = λ _ → tt
    ; comp-mono-r = λ _ → tt
    }

data SharedTag : Set where
  sharedTag : SharedTag

sharedPortSig₁ : PortSig oneThin2Cat SharedTag
sharedPortSig₁ =
  record
    { ℓDObj = lzero
    ; ℓDHom = lzero
    ; Displayed =
        LawDisplayedOn
          oneThin2Cat
          ⊤
          (λ _ → ⊤)
          tt
          (λ _ _ → tt)
    }

sharedPortSig₂ : PortSig oneThin2Cat SharedTag
sharedPortSig₂ =
  record
    { ℓDObj = lzero
    ; ℓDHom = lzero
    ; Displayed =
        LawDisplayedOn
          oneThin2Cat
          ⊤
          (λ _ → ⊤)
          tt
          (λ _ _ → tt)
    }

leftEntry : PortEntry oneThin2Cat
leftEntry = mkEntry sharedPortSig₁

rightEntry : PortEntry oneThin2Cat
rightEntry = mkEntry sharedPortSig₂

-- Same payload type, different concrete entries: uniqueness still holds.
_ : NoDupStack (leftEntry ∷⁺ [ rightEntry ])
_ =
  noDupCons
    (noDupSingleton {p = rightEntry})

-- Exact typed membership keeps track of the concrete entry.
_ : EntryMember rightEntry (leftEntry ∷ rightEntry ∷ [])
_ = thereEntry hereEntry

-- Raw membership follows the concrete entry itself.
_ : Member rightEntry (leftEntry ∷ rightEntry ∷ [])
_ = entryMember⇒member (thereEntry hereEntry)
