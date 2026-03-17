{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat.DeutschProduct where

-- Deutsch-style system category: independent product of the causality and local-reversibility law ports.
--
-- Base: locality-decorated physical kernels (see `Locality`).
-- Added law ports (independent):
-- - causality: flow preservation w.r.t. the fixed doctrine `GC`,
-- - local reversibility: pointwise order-isomorphisms in each fibre.
--
-- Packaged as a `PortStack` + `Template.Stack2Cat` (record-only surface).

open import LogOS.Prelude

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat as Deutsch2Cat

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  module Core = Deutsch2Cat.Deutsch2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS
  module Port = Core.Deutsch

  stack2Cat = Port.stack2Cat

  open Port public using
    ( stack
    ; Displayed
    ; WithPort
    ; forget
    ; baseObj
    ; baseHom
    )

  causal = Port.leftPort

  reversible = Port.rightPort
