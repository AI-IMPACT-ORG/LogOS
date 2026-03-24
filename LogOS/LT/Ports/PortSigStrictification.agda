{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortSigStrictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Explicit strict reindexing helpers for port signatures.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor.Strictification using (StrictThin2Functor)
open import LogOS.LT.DisplayedThin2Cat.Strictification using (reindexDisplayedStrictF)
open import LogOS.LT.Ports.PortSig using (PortSig; PortEntry; mkPortEntry; TagTy; Tagℓ; sig)

pullbackPortSig
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
    {ℓTag : Level} {Tag : Set ℓTag}
  → StrictThin2Functor C₁ C₂
  → PortSig C₂ Tag
  → PortSig C₁ Tag
pullbackPortSig SF sig =
  record
    { ℓDObj = PortSig.ℓDObj sig
    ; ℓDHom = PortSig.ℓDHom sig
    ; Displayed = reindexDisplayedStrictF SF (PortSig.Displayed sig)
    }

pullbackPortEntry
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → StrictThin2Functor C₁ C₂
  → PortEntry C₂
  → PortEntry C₁
pullbackPortEntry SF e =
  mkPortEntry
    (Tagℓ e)
    (TagTy e)
    (pullbackPortSig SF (sig e))
