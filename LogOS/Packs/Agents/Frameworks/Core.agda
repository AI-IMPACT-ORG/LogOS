{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.Core where

open import LogOS.Prelude

import LogOS.Computation.SchemeCategory as Cat

-- A “framework” is (minimally) just an `Interface` into a shared process.
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
    interface : Cat.Interface Input P

open Framework public
