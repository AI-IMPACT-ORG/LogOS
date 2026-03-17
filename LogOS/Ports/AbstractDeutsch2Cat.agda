{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat where

-- Deutsch-style physical systems as a thin 2-category (dependent-locality).
--
-- In v1.1 this is the canonical Deutsch-style implementation:
-- the local observation interface preorder may vary with the locality index.
--
-- The uniform special case is recovered by choosing a constant family of
-- observables `O : I → ConPreorder …` and a constant doctrine family `GC₀`.
--
-- Architectural reading:
-- `DependentLocalSemantics` is the index-dependent (“ultralocal-first”) semantics ledger:
-- you keep the same locality index `I`, but you allow the observable interface
-- preorder `O i` (and hence the doctrine) to depend on `i`.
--
-- The Deutsch-style category (LOGᴰ) is then the same port stack:
--   locality (baked into `LocalBoundary I O`)
--   + causality (flow preservation as a law-port)
--   + local reversibility (order-isomorphisms per region as a law-port)
--
-- Terminology note:
-- this **Deutsch-style category** (LOGᴰ) is a port-stack construction over physical
-- semantics. It is distinct from the “Deutsch object / CTD” universality shape
-- (weak terminality in `LOGᶠ`) packaged in `LogOS.Ports.Universality.CTD.Ledger`.
--
-- Structural comparison (in Apps):
-- `LogOS.Apps.TuringCategory.Bridge.AbstractDeutschToPar` provides a functorial
-- forgetting view `LOGᴰ PS → Par` (and an optional lift to `ParTracked`), which
-- is useful for comparing shapes without asserting a universality theorem.

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

open import LogOS.Prelude using (Level)

import LogOS.Ports.AbstractDeutsch2Cat.Locality as Locality2Cat
import LogOS.Ports.AbstractDeutsch2Cat.Causality as Causality2Cat
import LogOS.Ports.AbstractDeutsch2Cat.Reversibility as Reversibility2Cat

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  module Locality = Locality2Cat.Deutsch2CatLocal {ℓCode = ℓCode} PS
  module Causality = Causality2Cat.Deutsch2CatLocal {ℓCode = ℓCode} PS
  module Reversibility = Reversibility2Cat.Deutsch2CatLocal {ℓCode = ℓCode} PS
  module Deutsch = Reversibility
