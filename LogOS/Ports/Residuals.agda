{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Residuals where

-- Residuals vocabulary (residuation / adjoints).
--
-- Many “residual” notions across logic/PL/algebra share a single abstract core:
-- a right (or left) adjoint in a refinement preorder.
--
-- In LogOS this appears as a `GaloisConnection`:
--   L a ⊑ b    ↔    a ⊑ R b
--
-- Readings:
-- - `R` is a weakest-precondition / right-adjoint back-translation operator for `L`.
-- - `R ∘ L` is a closure (nucleus-style) (`GuardedClosure`) inducing an “effective” semantics.
--
-- This module is a small wrapper: it introduces residual-language aliases without
-- changing the core kernel.

open import LogOS.Prelude using (lsuc; _⊔_)

open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Flow using (GuardedClosure; Stable; elem)
open import LogOS.LT.Effectivity using (Effectivity; effectivityFromGalois)
open import LogOS.LT.Theorems.AbstractGaloisConnection using
  ( GaloisConnection
  ; L
  ; R
  ; adj
  ; unit
  ; counit
  ; closure
  ; RightImagePoint
  ; stableReflectiveImage
  ; pointwiseGalois
  )

-- Alias: “residual” is used as a synonym for “Galois connection” in some areas.
Residual : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
  → ConPreorder ℓACon ℓARel → ConPreorder ℓBCon ℓBRel
  → Set (lsuc (ℓACon ⊔ ℓARel ⊔ ℓBCon ⊔ ℓBRel))
Residual = GaloisConnection

residualForward : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
  {A : ConPreorder ℓACon ℓARel}
  {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → Con A → Con B
residualForward = L

residual : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
  {A : ConPreorder ℓACon ℓARel}
  {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → Con B → Con A
residual = R

residualClosure : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
  {A : ConPreorder ℓACon ℓARel}
  {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → GuardedClosure A
residualClosure = closure

-- View: a residual induces an effectivity calculus on the source boundary.
residualEffectivity
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → Effectivity A
residualEffectivity = effectivityFromGalois

-- PLT reading: residuals are weakest-precondition maps whose right image is the
-- effective / stable fragment induced by the residual closure.

weakestPrecondition : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
  {A : ConPreorder ℓACon ℓARel}
  {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → Con B → Con A
weakestPrecondition = residual

weakestPreconditionClosure : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
  {A : ConPreorder ℓACon ℓARel}
  {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → GuardedClosure A
weakestPreconditionClosure = residualClosure

weakestPreconditionEffectivity
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → Residual A B → Effectivity A
weakestPreconditionEffectivity = residualEffectivity

weakestPreconditionStableRepresentation
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : Residual A B)
  → (x : Stable {CP = A} (GuardedClosure.Flow (weakestPreconditionClosure G)))
  → RightImagePoint G (elem x)
weakestPreconditionStableRepresentation =
  stableReflectiveImage
