{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PreQuantum.Purification2Cat where

-- Purification witnesses as a displayed law port (Σ-decorated).
--
-- This turns `PurificationAssumptions` into a thin 2-category decoration:
-- each base morphism is equipped with a chosen purification witness.
--
-- Identity and composition use the explicit witness calculus bundled with
-- `PurificationAssumptions`, so the displayed structure does not silently
-- discard witness bookkeeping.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PreQuantum.Monoidal using (SymmetricMonoidalData; SymmetricMonoidalLaws)
open import LogOS.Ports.PreQuantum.Discard using (DiscardStructure)
open import LogOS.Ports.PreQuantum.Purification using
  ( PurificationWitness
  ; PurificationAssumptions
  ; purify-id
  ; purify-comp
  )

import LogOS.Ports.LawSlice2Cat as LawSlice

-- η-unit payload for the purification law-port (avoids Topℓ/⊤ footguns).
record PurificationOb : Set where
  constructor ttPurification

data PurificationTag : Set where
  purificationTag : PurificationTag

purificationTagId : ℕ
purificationTagId = 15

module Purification2CatLocal
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (M : SymmetricMonoidalData C)
  (ML : SymmetricMonoidalLaws M)
  (D : DiscardStructure C M)
  (P : PurificationAssumptions C M ML D)
  where

  open Thin2Cat C
  PurificationLaw
    : ∀ {A B}
    → Con (Hom A B)
    → Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel))
  PurificationLaw f = PurificationWitness C M ML D f

  module Port =
    LawSlice.Exports
      {C = C}
      {Tag = PurificationTag}
      purificationTagId
      PurificationOb
      PurificationLaw
      (purify-id P)
      (purify-comp P)

  open Port public using
    ( port2Cat
    ; singleton
    ; stack
    ; port
    ; Displayed
    ; WithPort
    ; forget
    )

open Purification2CatLocal public using
  ( port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  )
