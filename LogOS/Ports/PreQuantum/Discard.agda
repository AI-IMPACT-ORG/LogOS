{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PreQuantum.Discard where

-- Discard/environment structure as an explicit extra layer over a monoidal base.
--
-- This is the minimal “causality via discarding” interface:
-- discarding after a process is observationally the same as discarding before it.
--
-- (More structure, e.g. monoidality of discard, can be layered on top.)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PreQuantum.Monoidal using (SymmetricMonoidalData)

record DiscardStructure {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (M : SymmetricMonoidalData C)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  private
    I : Obj
    I = SymmetricMonoidalData.I M

  field
    discard : ∀ {A} → Con (Hom A I)

    discard-natural
      : ∀ {A B}
        (f : Con (Hom A B))
      → _≈_ (Hom A I)
          (discard {A = B} ∘ f)
          (discard {A = A})

open DiscardStructure public
