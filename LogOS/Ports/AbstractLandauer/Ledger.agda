{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractLandauer.Ledger where

-- Cost-law port (Landauer-style reading optional).
--
-- Design stance:
-- cost/grade structure is not part of the kernel or the base thin 2-category.
-- Instead it is supplied by an explicit assumption record, so that downstream
-- developments can remain honest about axiom strength.
--
-- This module is deliberately refinement-first:
-- - the neutral law is stated up to mutual refinement (`≈`),
-- - accumulation is stated as a refinement inequality (`⊑`),
-- - monotonicity along observational refinement is an explicit extra layer.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.AbstractLandauer.Core using
  ( CostProfile
  ; CostProfileMonotone
  )

record LandauerAssumptions
  {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (Scale : ConPreorder ℓScaleCon ℓScaleRel)
  (JP : JoinPrequantale Scale)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓScaleCon ⊔ ℓScaleRel)) where
  field
    profile : CostProfile C Scale JP

  open CostProfile profile public

open LandauerAssumptions public
-- Optional strengthening: monotonicity along observational refinement (2-cells).
record LandauerMonotone
  {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  (L : LandauerAssumptions C Scale JP)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓScaleCon ⊔ ℓScaleRel)) where
  field
    monotoneProfile : CostProfileMonotone (LandauerAssumptions.profile L)

  open CostProfileMonotone monotoneProfile public

open LandauerMonotone public
