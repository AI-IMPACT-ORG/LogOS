{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.Factorisation where

-- Opacity-specific wrapper for factorisations between private and public views.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Contracts using (Contract; ContractHom; mkContract)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts)
open import LogOS.LT.View using (View)
open import LogOS.LT.View.Factorisation using (FactorisesThrough; collapse; collapse-mono; commute)
open import LogOS.Ports.Opacity.Port using (OpacityPort; toView; opacityKernel)

record OpacityFactorisation
  {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
  {X : Set ℓX}
  {O₁ : ConPreorder ℓC₁ ℓR₁}
  {O₂ : ConPreorder ℓC₂ ℓR₂}
  (privatePort : OpacityPort X O₁)
  (publicPort : OpacityPort X O₂)
  : Set (lsuc (ℓX ⊔ ℓC₁ ⊔ ℓR₁ ⊔ ℓC₂ ⊔ ℓR₂)) where
  field
    factorisation : FactorisesThrough (toView privatePort) (toView publicPort)

  privateView : View X O₁
  privateView = toView privatePort

  publicView : View X O₂
  publicView = toView publicPort

open OpacityFactorisation public

privateContract
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {privatePort : OpacityPort X O₁}
    {publicPort : OpacityPort X O₂}
  → OpacityFactorisation privatePort publicPort
  → Con O₁
  → Contract {ℓ = ℓC₁} {ℓRel = ℓR₁} {ℓCode = ℓX}
privateContract {privatePort = privatePort} _ c = mkContract (opacityKernel privatePort) c

publicContract
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {privatePort : OpacityPort X O₁}
    {publicPort : OpacityPort X O₂}
  → OpacityFactorisation privatePort publicPort
  → Con O₂
  → Contract {ℓ = ℓC₂} {ℓRel = ℓR₂} {ℓCode = ℓX}
publicContract {publicPort = publicPort} _ c = mkContract (opacityKernel publicPort) c

factorisationKernelHom
  : ∀ {ℓX ℓC ℓR : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC ℓR}
    {O₂ : ConPreorder ℓC ℓR}
    {privatePort : OpacityPort X O₁}
    {publicPort : OpacityPort X O₂}
  → (F : OpacityFactorisation privatePort publicPort)
  → KernelHom (opacityKernel privatePort) (opacityKernel publicPort)
factorisationKernelHom F =
  mkKernelHomParts
    (record
      { map∂ = collapse (factorisation F)
      ; map∂-mono = collapse-mono (factorisation F)
      })
    (record
      { mapCode = λ x → x
      ; decode-mapCode = commute (factorisation F)
      })

factorisationContractHom
  : ∀ {ℓX ℓC ℓR : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC ℓR}
    {O₂ : ConPreorder ℓC ℓR}
    {privatePort : OpacityPort X O₁}
    {publicPort : OpacityPort X O₂}
  → (F : OpacityFactorisation privatePort publicPort)
  → ∀ {c₁ : Con O₁} {c₂ : Con O₂}
  → _⊑_ O₂ c₂ (collapse (factorisation F) c₁)
  → ContractHom (privateContract F c₁) (publicContract F c₂)
factorisationContractHom F law = lift (factorisationKernelHom F , law)
