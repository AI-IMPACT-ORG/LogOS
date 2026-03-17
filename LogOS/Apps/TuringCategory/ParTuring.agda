{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.ParTuring where

-- Turing-object packaging for the canonical partial-map model `Par`.
--
-- Design stance (LogOS discipline):
-- - A CH(2008) “Turing object” is strong data: it amounts to an explicit
--   indexing/compilation discipline into a fixed object `U`.
-- - For the full partial-map model (all monotone partial maps between all
--   preorders), such an indexer is not something we can (or should) conjure
--   implicitly; it is semantics content and must be injected as an explicit
--   assumption/ledger.
--
-- Therefore this module provides *only* the clean packaging layer:
-- given a chosen `U` and a CH(2008) `TuringObjectᵇ` on `Par`, we obtain a
-- bundled `TuringCategoryᵇ`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)

import LogOS.Apps.TuringCategory.CH2008 as CH
open import LogOS.Apps.TuringCategory.ParCH2008 using (parRC; parCartesian)

record ParTuringLedger {ℓCon ℓRel : Level} : Set (lsuc (lsuc (ℓCon ⊔ ℓRel))) where
  field
    U  : ConPreorder ℓCon ℓRel
    TU : CH.TuringObjectᵇ (parRC {ℓCon} {ℓRel}) (parCartesian {ℓCon} {ℓRel}) U

open ParTuringLedger public

parTuringCategoryᵇ
  : ∀ {ℓCon ℓRel : Level}
  → ParTuringLedger {ℓCon} {ℓRel}
  → CH.TuringCategoryᵇ
      {ℓObj = lsuc (ℓCon ⊔ ℓRel)}
      {ℓHomCon = ℓCon ⊔ ℓRel}
      {ℓHomRel = ℓCon ⊔ ℓRel}
parTuringCategoryᵇ {ℓCon} {ℓRel} L =
  record
    { RC = parRC {ℓCon} {ℓRel}
    ; cart = parCartesian {ℓCon} {ℓRel}
    ; U = U L
    ; TU = TU L
    }
