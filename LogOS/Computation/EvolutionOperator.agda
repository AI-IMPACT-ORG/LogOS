{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.EvolutionOperator where

open import LogOS.Prelude

-- A minimal, reusable “time evolution operator” interface.
--
-- This is deliberately generic: it packages an embedding of an internal stepper
-- into an abstract endomap, together with the commuting diagram.

record EvolOperator {ℓC ℓH : Level} (Code : Set ℓC) (step : Code → Code)
  : Set (lsuc (ℓC ⊔ ℓH)) where
  field
    H          : Set ℓH
    embed      : Code → H
    Op         : H → H
    intertwine : ∀ c → embed (step c) ≡ Op (embed c)

open EvolOperator public

-- Optional acceptance layer (kept separate so pure “intertwiner” use-cases do
-- not have to commit to an acceptance semantics).

record EvolOperatorAcc {ℓC ℓH ℓA : Level} (Code : Set ℓC) (step : Code → Code)
  : Set (lsuc (ℓC ⊔ ℓH ⊔ ℓA)) where
  field
    EO  : EvolOperator {ℓC = ℓC} {ℓH = ℓH} Code step
    Acc : EvolOperator.H EO → Set ℓA

  open EvolOperator EO public
