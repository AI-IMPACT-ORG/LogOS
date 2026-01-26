{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.Core where

open import LogOS.Prelude

import LogOS.Computation.SchemeCategory as Cat

-- A “framework” is (minimally) just a `Choice` into a shared process.
--
-- This matches the repo’s universality story: many paradigms differ only by
-- compiler + fuel, while sharing a common operational semantics (“process”).

record Framework
  {ℓI ℓO ℓC ℓQ : Level}
  (Input : Set ℓI)
  (Output : Set ℓO)
  (P : Cat.Process {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} Output)
  : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓC ⊔ ℓQ)) where
  field
    choice : Cat.Choice Input P

open Framework public

