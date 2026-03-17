{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Contracts.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-facing contract laws extracted from `LogOS.LT.Contracts`.
--
-- This module names the existing transport and compatibility facts explicitly,
-- so shells do not need to repackage them ad hoc.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; mapCode)
open import LogOS.LT.Contracts using
  ( _⊨_[_]
  ; Contract
  ; ContractHom
  ; ContractLaw
  ; KernelOf
  ; ConOf
  ; hom
  ; compat
  ; idContractHom
  ; _∘Contract_
  ; models-map
  ; models-map-contract
  )

KernelModelsMapLaw
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (h : KernelHom K K')
  → Set _
KernelModelsMapLaw {K = K} {K' = K'} h =
  ∀ {γ c}
  → K ⊨ γ [ c ]
  → K' ⊨ mapCode h γ [ map∂ h c ]

kernelModelsMapLaw
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (h : KernelHom K K')
  → KernelModelsMapLaw h
kernelModelsMapLaw h = models-map h

ContractCompatibilityLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (X Y : Contract {ℓ} {ℓRel} {ℓCode})
  → KernelHom (KernelOf X) (KernelOf Y)
  → Set ℓRel
ContractCompatibilityLaw = ContractLaw

idContractCompatibilityLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    (X : Contract {ℓ} {ℓRel} {ℓCode})
  → ContractCompatibilityLaw X X (hom (idContractHom X))
idContractCompatibilityLaw X = compat (idContractHom X)

composeContractCompatibilityLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    {X Y Z : Contract {ℓ} {ℓRel} {ℓCode}}
    (g : ContractHom Y Z)
    (f : ContractHom X Y)
  → ContractCompatibilityLaw X Z (hom (g ∘Contract f))
composeContractCompatibilityLaw g f = compat (g ∘Contract f)

contractModelsMapLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    {X Y : Contract {ℓ} {ℓRel} {ℓCode}}
    (h : ContractHom X Y)
  → ∀ {γ}
  → KernelOf X ⊨ γ [ ConOf X ]
  → KernelOf Y ⊨ mapCode (hom h) γ [ ConOf Y ]
contractModelsMapLaw h = models-map-contract h
