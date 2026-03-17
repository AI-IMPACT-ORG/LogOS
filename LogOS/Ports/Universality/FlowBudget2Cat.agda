{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.FlowBudget2Cat where

-- Port composition: Flow + Budget bus.
--
-- This is the “weak coupling” pattern made systematic outside the kernel:
-- - `Flow` is a displayed layer over `LOG` (closure choice + preservation),
-- - `Budget` is a displayed layer over `LOG` (explicit numeric observation + transport),
-- - their product is a displayed layer over the same base, and
-- - decoration yields a thin 2-category with the *same* observational refinement
--   on underlying kernel morphisms (in base `LOG`: boundary-driven `_⇒∂_`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
import LogOS.LT.LOG.Flow2Cat as Flow2Cat
import LogOS.Ports.Universality.BudgetBus2Cat as BudgetBus2Cat
import LogOS.LT.Ports.Template.Stack2Cat as Template

module Ports
  {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  =
  Template.BinarySingletonStackExports
    (Flow2Cat.singleton {ℓ} {ℓRel} {ℓCode})
    (BudgetBus2Cat.singleton {ℓ} {ℓRel} {ℓCode} Budget)
open Ports public using
  ( stack2Cat
  ; stack
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )
