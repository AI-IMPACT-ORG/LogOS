{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.PhysicalOptional.Landauer where

-- Curated optional API for thermodynamic structure over the causal base.
--
-- The actual-cost lower-bound surface is primary, but remains explicitly
-- conditional on a chosen observational bridge. `CostBound` is retained only as
-- a secondary corollary layer, recovered on the curated surface via
-- `boundProof`.

open import LogOS.Prelude using (Level)
open import LogOS.Ports.AbstractCausalLandauer2Cat public using
  ( C
  ; Scale
  ; JP
  ; CausalLandauerAssumptions
  ; landauer
  ; landauerPort
  ; stack2Cat
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )

open import LogOS.Ports.AbstractLandauer.Ledger public using
  ( LandauerAssumptions )
open import LogOS.Ports.AbstractLandauer2Cat public using
  ( LandauerTag
  ; singleton
  ; CostBound
  ; boundOf
  ; boundProof
  ; CostBoundRefines
  ; CostBoundPreorder
  ; totalCostBound
  ; TotalCostBoundRefines
  ; TotalCostBoundPreorder
  )
open import LogOS.Ports.Opacity.ObservationAction public using
  ( ObservationAction
  ; processFactorisation
  )
open import LogOS.Ports.Valuation.CompressionValuation public using
  ( CompressionValuation
  ; singleCompression
  )
open import LogOS.Ports.AbstractLandauerObservational public using
  ( ObservationalCostBridge
  ; compressionValue
  ; countLoss≤cost
  ; singleCompression≤cost
  )

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
import LogOS.LT.Ports.PortStack.Unique as PortStackUnique
import LogOS.Ports.AbstractCausalLandauer2Cat as CausalLandauer2Cat

CausalLandauerUniqueStack
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalLandauerAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → PortStackUnique.UniquePortStack
      (CausalLandauer2Cat.C {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
CausalLandauerUniqueStack PS Q A =
  PortStackUnique.mkUniquePortStack
    (CausalLandauer2Cat.CausalLandauerStack PS Q A)
    PortStackUnique.noDupSingleton

CausalLandauerUniquePort
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalLandauerAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → PortStackUnique.UniquePort
      _
      (CausalLandauer2Cat.CausalLandauerStack PS Q A)
CausalLandauerUniquePort PS Q A =
  PortStackUnique.mkUniquePort
    (CausalLandauer2Cat.landauerPort PS Q A)
    (PortStackUnique.UniquePortStack.stackNoDup (CausalLandauerUniqueStack PS Q A))
