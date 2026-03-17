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
open import LogOS.LT.Ports.PortSig using (PortEntry; PortLabel; PortSig; mkEntry)
open import LogOS.LT.Ports.PortStack.Raw using
  ( NoDupStack
  ; [_]
  ; _∷⁺_
  ; []
  ; _∷_
  ; Member
  ; EntryMember
  ; hereEntry
  ; there
  ; thereEntry
  ; entryMember⇒member
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

leftLabel : PortLabel
leftLabel = 2001

rightLabel : PortLabel
rightLabel = 2002

sharedPortSig₁ : PortSig oneThin2Cat leftLabel SharedTag
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

sharedPortSig₂ : PortSig oneThin2Cat rightLabel SharedTag
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

leftLabel≠rightLabel
  : Member leftLabel (rightEntry ∷ [])
  → ⊥ {lzero}
leftLabel≠rightLabel (there m) = impossible m
  where
    impossible : Member leftLabel [] → ⊥ {lzero}
    impossible ()

-- Same payload type, different first-order labels: uniqueness still holds.
_ : NoDupStack (leftEntry ∷⁺ [ rightEntry ])
_ =
  noDupCons
    {p = leftEntry}
    {ps = [ rightEntry ]}
    leftLabel≠rightLabel
    noDupSingleton

-- Exact typed membership keeps track of the concrete entry.
_ : EntryMember rightEntry (leftEntry ∷ rightEntry ∷ [])
_ = thereEntry hereEntry

-- Raw membership only sees the first-order label extracted from that entry.
_ : Member rightLabel (leftEntry ∷ rightEntry ∷ [])
_ = entryMember⇒member (thereEntry hereEntry)
