{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.PortStackUniquePublic where

open import LogOS.Prelude
open import LogOS.API.Kernel using (NoDupStack; UniquePort; UniquePortStack)
open import LogOS.API.Ports.PhysicalOptional.Landauer using
  ( CausalLandauerAssumptions )
open import LogOS.API.Ports.PhysicalOptional.PreQuantum using
  ( CausalPreQuantumAssumptions )
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
import LogOS.API.Ports.PhysicalOptional.Landauer as OptionalLandauer
import LogOS.API.Ports.PhysicalOptional.PreQuantum as OptionalPreQuantum
import LogOS.Ports.AbstractLandauer2Cat as Landauer2Cat
import LogOS.Ports.PreQuantum.AbstractCausalPreQuantum2Cat as CausalPreQuantum2Cat
import LogOS.Ports.PreQuantum.Purification2Cat as Purification2Cat

-- Covers `LogOS.API.Ports.PhysicalOptional.Landauer.CausalLandauerUniqueStack`.
CausalLandauerUniqueStack-noDup
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalLandauerAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → NoDupStack
      (UniquePortStack.rawStack (OptionalLandauer.CausalLandauerUniqueStack PS Q A))
CausalLandauerUniqueStack-noDup PS Q A =
  UniquePortStack.stackNoDup (OptionalLandauer.CausalLandauerUniqueStack PS Q A)

CausalLandauerUniquePort-noDup
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalLandauerAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → NoDupStack
      (UniquePortStack.rawStack (OptionalLandauer.CausalLandauerUniqueStack PS Q A))
CausalLandauerUniquePort-noDup PS Q A =
  UniquePort.noDup (OptionalLandauer.CausalLandauerUniquePort PS Q A)

CausalPreQuantumUniqueStack-noDup
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalPreQuantumAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → NoDupStack
      (UniquePortStack.rawStack (OptionalPreQuantum.CausalPreQuantumUniqueStack PS Q A))
CausalPreQuantumUniqueStack-noDup PS Q A =
  UniquePortStack.stackNoDup (OptionalPreQuantum.CausalPreQuantumUniqueStack PS Q A)

landauerUniquePort-noDup
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalPreQuantumAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → NoDupStack
      (CausalPreQuantum2Cat.CausalPreQuantumStack PS Q A)
landauerUniquePort-noDup PS Q A =
  UniquePort.noDup (OptionalPreQuantum.landauerUniquePort PS Q A)

purificationUniquePort-noDup
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalPreQuantumAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → NoDupStack
      (CausalPreQuantum2Cat.CausalPreQuantumStack PS Q A)
purificationUniquePort-noDup PS Q A =
  UniquePort.noDup (OptionalPreQuantum.purificationUniquePort PS Q A)

_ : Landauer2Cat.LandauerTag
_ = Landauer2Cat.landauerTag

_ : Purification2Cat.PurificationTag
_ = Purification2Cat.purificationTag
