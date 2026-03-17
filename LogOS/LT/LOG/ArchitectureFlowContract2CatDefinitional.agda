{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureFlowContract2CatDefinitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude using (Level; _≡_)
open import LogOS.LT.DisplayedThin2Cat using
  ( ProductDisplayed
  ; forgetProductLeft
  ; forgetProductRight
  )

import LogOS.LT.LOG.ArchitectureFlowContract2Cat as ArchitectureFlowContract
import LogOS.LT.LOG.ImplementationFlow2Cat.Core as FlowArchitecture
import LogOS.LT.LOG.ImplementationContract2Cat.Core as ContractArchitecture
import LogOS.LT.Ports.PortStack.Raw as PortStack

Displayed-product
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ArchitectureFlowContract.Displayed {ℓ} {ℓRel} {ℓCode}
    ≡
    ProductDisplayed
      (FlowArchitecture.FlowDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
      (ContractArchitecture.ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
Displayed-product {ℓ} {ℓRel} {ℓCode} =
  ArchitectureFlowContract.Ports.Displayed-product {ℓ} {ℓRel} {ℓCode}

forgetFlow-product
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.forgetPort (ArchitectureFlowContract.Ports.leftPort {ℓ} {ℓRel} {ℓCode})
    ≡
    forgetProductLeft
      (FlowArchitecture.FlowDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
      (ContractArchitecture.ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
forgetFlow-product {ℓ} {ℓRel} {ℓCode} =
  ArchitectureFlowContract.Ports.forgetLeft-product {ℓ} {ℓRel} {ℓCode}

forgetContract-product
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.forgetPort (ArchitectureFlowContract.Ports.rightPort {ℓ} {ℓRel} {ℓCode})
    ≡
    forgetProductRight
      (FlowArchitecture.FlowDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
      (ContractArchitecture.ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
forgetContract-product {ℓ} {ℓRel} {ℓCode} =
  ArchitectureFlowContract.Ports.forgetRight-product {ℓ} {ℓRel} {ℓCode}
