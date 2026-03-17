{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.RawDefinitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Bookkeeping equalities for the explicit raw/shadowing stack lane.
--
-- The raw stack surface keeps duplicate-tag, leftmost-resolution machinery
-- reachable. Equality of raw membership witnesses is intentionally quarantined
-- here rather than exposed as part of the ordinary public stack facade.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Ports.PortSig using (PortEntry; LabelOf)
open import LogOS.LT.Ports.PortStack.Raw using
  ( Listω
  ; []
  ; _∷_
  ; Member
  ; NoDupTags
  ; NoDupTagsStep
  )

head-not-in-rest
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {e : PortEntry C}
    {es : Listω (PortEntry C)}
  → NoDupTags (e ∷ es)
  → Member (LabelOf e) es
  → ⊥
head-not-in-rest noDup = NoDupTagsStep.notInRest noDup
