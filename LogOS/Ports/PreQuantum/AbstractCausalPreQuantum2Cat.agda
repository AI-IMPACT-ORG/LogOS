{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PreQuantum.AbstractCausalPreQuantum2Cat where

-- Causal + Landauer + purification as an explicitly stacked port 2-category.
-- Base: the dependent causal physical category `LOGᶜ` (locality + causality).
-- Extra layers (independent law ports):
-- - Landauer cost bounds (`Landauer2Cat`): explicit scale bounds on adapters.
-- - Purification witnesses (`Purification2Cat`): chosen dilation witnesses per adapter.
--
-- The result is a Σ-decoration of a displayed product over `LOGᶜ`, so
-- irreversible arrows remain first-class before purification is asked for.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

open import LogOS.Ports.Valuation.QAdapter using (QAdapter)

import LogOS.Ports.AbstractLandauer2Cat as Landauer2Cat
import LogOS.Ports.AbstractCausalLandauer2Cat as CausalLandauer2Cat

open import LogOS.Ports.PreQuantum.Monoidal using (SymmetricMonoidalData; SymmetricMonoidalLaws)
open import LogOS.Ports.PreQuantum.Discard using (DiscardStructure)
open import LogOS.Ports.PreQuantum.Purification using
  ( PurificationWitness
  ; PurificationAssumptions
  ; purify-id
  ; purify-comp
  )
import LogOS.Ports.PreQuantum.Purification2Cat as Purification2Cat

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.PortStack.Unique as PortStackUnique
import LogOS.LT.Ports.Template.LawSingleton2Cat as LawSingleton
import LogOS.LT.Ports.Template.Stack2Cat as Template

module CausalPreQuantum2CatLocal
  {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
  (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  (Q : QAdapter ℓQ)
  where

  module CausalLandauer = CausalLandauer2Cat.CausalLandauer2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} {ℓQ} PS Q

  C : Thin2Cat _ _ _
  C = CausalLandauer.C

  Scale = CausalLandauer.Scale
  JP = CausalLandauer.JP

  record CausalPreQuantumAssumptions
    : Set (lsuc (lsuc ((lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓCode)) ⊔ ℓQ))) where
    field
      causalLandauer : CausalLandauer.CausalLandauerAssumptions

      SM : SymmetricMonoidalData C
      SML : SymmetricMonoidalLaws SM

      discard : DiscardStructure C SM
      purification : PurificationAssumptions C SM SML discard

  open CausalPreQuantumAssumptions public

  purificationSingleton
    : (A : CausalPreQuantumAssumptions)
    → PortStack.SingletonPort C Purification2Cat.PurificationTag
  purificationSingleton A =
    Purification2Cat.singleton
      {C = C}
      (SM A)
      (SML A)
      (discard A)
      (purification A)

  purificationPortSig
    : (A : CausalPreQuantumAssumptions)
    → PortSig.PortSig C Purification2Cat.PurificationTag
  purificationPortSig A =
    LawSingleton.lawPortSig
      {C = C}
      {Tag = Purification2Cat.PurificationTag}
      Purification2Cat.PurificationOb
      (PurificationWitness C (SM A) (SML A) (discard A))
      (purify-id (purification A))
      (purify-comp (purification A))

  landauerSingleton
    : (A : CausalPreQuantumAssumptions)
    → PortStack.SingletonPort C Landauer2Cat.LandauerTag
  landauerSingleton A =
    Landauer2Cat.singleton
      {C = C}
      (CausalLandauer.landauer (causalLandauer A))

  landauerPortSig
    : (A : CausalPreQuantumAssumptions)
    → PortSig.PortSig C Landauer2Cat.LandauerTag
  landauerPortSig A =
    LawSingleton.lawPortSig
      {C = C}
      {Tag = Landauer2Cat.LandauerTag}
      Landauer2Cat.LandauerOb
      (Landauer2Cat.CostBound
        (CausalLandauer.landauer (causalLandauer A)))
      (Landauer2Cat.idCostBound
        (CausalLandauer.landauer (causalLandauer A)))
      (Landauer2Cat.composeCostBound
        (CausalLandauer.landauer (causalLandauer A)))

  landauerEntry
    : (A : CausalPreQuantumAssumptions)
    → PortSig.PortEntry C
  landauerEntry A = PortSig.mkEntry (landauerPortSig A)

  purificationEntry
    : (A : CausalPreQuantumAssumptions)
    → PortSig.PortEntry C
  purificationEntry A = PortSig.mkEntry (purificationPortSig A)

  CausalPreQuantumStack
    : CausalPreQuantumAssumptions
    → PortStack.PortStack C
  CausalPreQuantumStack A =
    purificationEntry A PortStack.∷⁺ PortStack.[ landauerEntry A ]

  CausalPreQuantumStack-noDup
    : (A : CausalPreQuantumAssumptions)
    → PortStack.NoDupStack (CausalPreQuantumStack A)
  CausalPreQuantumStack-noDup A =
    PortStackUnique.noDupCons
      (PortStackUnique.noDupSingleton {p = landauerEntry A})

  CausalPreQuantumUniqueStack
    : CausalPreQuantumAssumptions
    → PortStackUnique.UniquePortStack C
  CausalPreQuantumUniqueStack A =
    PortStackUnique.mkUniquePortStack
      (CausalPreQuantumStack A)
      (CausalPreQuantumStack-noDup A)

  landauerPort
    : (A : CausalPreQuantumAssumptions)
    → PortStack.HasPort (landauerEntry A) (CausalPreQuantumStack A)
  landauerPort A =
    PortStack.hasSecond

  purificationPort
    : (A : CausalPreQuantumAssumptions)
    → PortStack.HasPort
        (purificationEntry A)
        (CausalPreQuantumStack A)
  purificationPort A =
    PortStack.hasHead

  landauerUniquePort
    : (A : CausalPreQuantumAssumptions)
    → PortStackUnique.UniquePort
        (landauerEntry A)
        (CausalPreQuantumStack A)
  landauerUniquePort A =
    PortStackUnique.mkUniquePort
      (landauerPort A)
      (CausalPreQuantumStack-noDup A)

  purificationUniquePort
    : (A : CausalPreQuantumAssumptions)
    → PortStackUnique.UniquePort
        (purificationEntry A)
        (CausalPreQuantumStack A)
  purificationUniquePort A =
    PortStackUnique.mkUniquePort
      (purificationPort A)
      (CausalPreQuantumStack-noDup A)

  stack2Cat
    : CausalPreQuantumAssumptions
    → Template.Stack2Cat C
  stack2Cat A =
    Template.mkBinaryStack2Cat
      (purificationEntry A)
      (landauerEntry A)

  module Port (A : CausalPreQuantumAssumptions) =
    Template.StackExports (stack2Cat A)

  open Port public using
    ( stack
    ; Displayed
    ; WithPort
    ; forget
    ; baseObj
    ; baseHom
    )

open CausalPreQuantum2CatLocal public using
  ( C
  ; Scale
  ; JP
  ; CausalPreQuantumAssumptions
  ; CausalPreQuantumStack
  ; CausalPreQuantumStack-noDup
  ; CausalPreQuantumUniqueStack
  ; landauerPort
  ; landauerUniquePort
  ; purificationPort
  ; purificationUniquePort
  ; stack2Cat
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )
