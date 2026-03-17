{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Cat.WeakTerminal where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

-- --------------------------------------------------------------------------
-- Universality: weak terminality (existence of maps into a chosen object).
--
-- This is the minimal categorical shape used by the CTD-style “universal
-- simulator” story: for each object (or each object in a chosen family), there
-- exists at least one 1-cell into the designated universal object.
--
-- No uniqueness is assumed; if you want uniqueness up to refinement/equivalence
-- that is additional structure (and boundary-dependent).

record WeakTerminal
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    U     : Obj
    toU   : (A : Obj) → Con (Hom A U)

open WeakTerminal public
record WeakTerminalCone
  {ℓI ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (I : Set ℓI)
  (F : I → Thin2Cat.Obj C)
  : Set (lsuc (ℓI ⊔ ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    U     : Obj
    toU   : (i : I) → Con (Hom (F i) U)

open WeakTerminalCone public

