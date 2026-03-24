{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.PortStackLeftmostResolution where

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Ports.PortSig using (PortSig; PortEntry; mkPortEntry)
open import LogOS.LT.Ports.PortStack.Raw using (Listω; _∷_; Member; here)

leftmost-duplicate-resolution
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {ℓTag : Level}
    {Tag : Set ℓTag}
    {sig₁ sig₂ : PortSig C Tag}
    {rest : Listω (PortEntry C)}
  → Member
      (mkPortEntry ℓTag Tag sig₁)
      (mkPortEntry ℓTag Tag sig₁ ∷ mkPortEntry ℓTag Tag sig₂ ∷ rest)
leftmost-duplicate-resolution = here
