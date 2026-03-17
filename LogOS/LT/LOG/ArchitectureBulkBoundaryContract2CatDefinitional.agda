{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureBulkBoundaryContract2CatDefinitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude using (Level; _≡_)
open import LogOS.LT.DisplayedThin2Cat using
  ( ProductDisplayed
  ; forgetProductLeft
  ; forgetProductRight
  )

import LogOS.LT.LOG.ArchitectureBulkBoundary2Cat as BulkBoundary
import LogOS.LT.LOG.ArchitectureBulkBoundaryContract2Cat as ArchitectureBulkBoundaryContract
import LogOS.LT.LOG.ImplementationContract2Cat.Core as ContractArchitecture
import LogOS.LT.Ports.PortStack.Raw as PortStack

Displayed-product
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ArchitectureBulkBoundaryContract.Displayed {ℓ} {ℓRel} {ℓCode}
    ≡
    ProductDisplayed
      (BulkBoundary.Displayed {ℓ} {ℓRel} {ℓCode})
      (ContractArchitecture.ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
Displayed-product {ℓ} {ℓRel} {ℓCode} =
  ArchitectureBulkBoundaryContract.Ports.Displayed-product {ℓ} {ℓRel} {ℓCode}

forgetBulkBoundary-product
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.forgetPort (ArchitectureBulkBoundaryContract.Ports.leftPort {ℓ} {ℓRel} {ℓCode})
    ≡
    forgetProductLeft
      (BulkBoundary.Displayed {ℓ} {ℓRel} {ℓCode})
      (ContractArchitecture.ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
forgetBulkBoundary-product {ℓ} {ℓRel} {ℓCode} =
  ArchitectureBulkBoundaryContract.Ports.forgetLeft-product {ℓ} {ℓRel} {ℓCode}

forgetContract-product
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.forgetPort (ArchitectureBulkBoundaryContract.Ports.rightPort {ℓ} {ℓRel} {ℓCode})
    ≡
    forgetProductRight
      (BulkBoundary.Displayed {ℓ} {ℓRel} {ℓCode})
      (ContractArchitecture.ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
forgetContract-product {ℓ} {ℓRel} {ℓCode} =
  ArchitectureBulkBoundaryContract.Ports.forgetRight-product {ℓ} {ℓRel} {ℓCode}
