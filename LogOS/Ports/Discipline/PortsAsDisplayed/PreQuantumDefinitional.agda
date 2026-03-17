{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.PreQuantumDefinitional where

open import LogOS.Prelude using (Level; _≡_)
open import LogOS.LT.DisplayedThin2Cat using
  ( DecoratedThin2Cat
  ; forgetDecorated
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
open import LogOS.Ports.PreQuantum.Monoidal using (SymmetricMonoidalData; SymmetricMonoidalLaws)
open import LogOS.Ports.PreQuantum.Discard using (DiscardStructure)
open import LogOS.Ports.PreQuantum.Purification using (PurificationAssumptions)

import LogOS.Ports.PreQuantum.Discard2Cat as Discard2Cat
import LogOS.Ports.PreQuantum.Purification2Cat as Purification2Cat
import LogOS.Ports.PreQuantum.AbstractCausalPreQuantum2Cat as CausalPreQuantum2Cat
import LogOS.LT.Ports.Template.Singleton2CatDefinitional as SingletonDef
import LogOS.LT.Ports.Template.Stack2CatDefinitional as StackDef

WithDiscard-def
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (CL : Thin2CatLaws C)
    (M : SymmetricMonoidalData C)
  → Discard2Cat.WithPort CL M
    ≡
    DecoratedThin2Cat (Discard2Cat.DiscardDisplayed CL M)
WithDiscard-def CL M = SingletonDef.withPort≡ (Discard2Cat.port2Cat CL M)

forgetDiscard-def
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (CL : Thin2CatLaws C)
    (M : SymmetricMonoidalData C)
  → Discard2Cat.forget CL M
    ≡
    forgetDecorated (Discard2Cat.DiscardDisplayed CL M)
forgetDiscard-def CL M = SingletonDef.forget≡ (Discard2Cat.port2Cat CL M)

WithPurification-def
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (M : SymmetricMonoidalData C)
    (ML : SymmetricMonoidalLaws M)
    (D : DiscardStructure C M)
    (P : PurificationAssumptions C M ML D)
  → Purification2Cat.WithPort M ML D P
    ≡
    DecoratedThin2Cat (Purification2Cat.Displayed M ML D P)
WithPurification-def M ML D P = SingletonDef.withPort≡ (Purification2Cat.port2Cat M ML D P)

forgetPurification-def
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (M : SymmetricMonoidalData C)
    (ML : SymmetricMonoidalLaws M)
    (D : DiscardStructure C M)
    (P : PurificationAssumptions C M ML D)
  → Purification2Cat.forget M ML D P
    ≡
    forgetDecorated (Purification2Cat.Displayed M ML D P)
forgetPurification-def M ML D P = SingletonDef.forget≡ (Purification2Cat.port2Cat M ML D P)

LOGᶜᵖ-def
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalPreQuantum2Cat.CausalPreQuantumAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → CausalPreQuantum2Cat.WithPort {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q A
    ≡
    DecoratedThin2Cat (CausalPreQuantum2Cat.Displayed {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q A)
LOGᶜᵖ-def PS Q A = StackDef.withPort≡ (CausalPreQuantum2Cat.stack2Cat PS Q A)

forgetCausalPreQuantum-def
  : ∀ {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
    (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
    (Q : QAdapter ℓQ)
    (A : CausalPreQuantum2Cat.CausalPreQuantumAssumptions {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q)
  → CausalPreQuantum2Cat.forget {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q A
    ≡
    forgetDecorated (CausalPreQuantum2Cat.Displayed {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q A)
forgetCausalPreQuantum-def PS Q A = StackDef.forget≡ (CausalPreQuantum2Cat.stack2Cat PS Q A)
