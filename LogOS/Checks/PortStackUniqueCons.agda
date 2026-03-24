{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.PortStackUniqueCons where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using (LawDisplayedOn)
open import LogOS.LT.Ports.PortSig using (PortEntry; PortSig; mkEntry)
open import LogOS.LT.Ports.PortStack.Raw using (NoDupStack; [_]; _∷⁺_)
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

data HeadTag : Set where
  headTag : HeadTag

data TailTag : Set where
  tailTag : TailTag

headPortSig : PortSig oneThin2Cat HeadTag
headPortSig =
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

tailPortSig : PortSig oneThin2Cat TailTag
tailPortSig =
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

headEntry : PortEntry oneThin2Cat
headEntry = mkEntry headPortSig

tailEntry : PortEntry oneThin2Cat
tailEntry = mkEntry tailPortSig

_ : NoDupStack (headEntry ∷⁺ [ tailEntry ])
_ =
  noDupCons
    (noDupSingleton {p = tailEntry})
