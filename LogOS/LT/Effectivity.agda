{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Effectivity where
-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Effective-semantics calculus (not domain-specific).
--
-- This module packages the small amount of structure that repeatedly appears
-- across PL/math applications in LogOS:
--
-- - a guarded closure `Flow` on an observation preorder (normalisation / saturation),
-- - reflection into stable points (`quot` / stable completion),
-- - and the induced “effective observation” (`Flow ∘ decode`) and packets.
--
-- QFT language (renormalisation, perturbation series, etc.) is only one reading
-- of this calculus; the underlying infrastructure is general.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; elem)
import LogOS.LT.Reflection as Ref using (quot; quot⊣evalm)

open import LogOS.LT.Kernel using (Kernel; bnd; Code)
open import LogOS.LT.Hom.Core using (KernelHom)
open import LogOS.LT.HomFlow using (KernelHomFlow)

import LogOS.LT.LOG.ArchitectureQuote2Cat as Quote
import LogOS.LT.Theorems.Effectivisation as Eff
import LogOS.LT.Theorems.EffectivePackets as Pack
import LogOS.LT.Theorems.AbstractGaloisConnection as Gal
import LogOS.LT.Theorems.StableCompletion as StableComp

-- Boundary-level packaging: a guarded closure together with its stable-point
-- reflection vocabulary.
record Effectivity {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    GC : GuardedClosure CP

  normalize : Con CP → Con CP
  normalize = Flow GC

  StablePoint : Set (lsuc (ℓCon ⊔ ℓRel))
  StablePoint = Stable {CP = CP} normalize

  quot : Con CP → StablePoint
  quot = Ref.quot GC

  eval : StablePoint → Con CP
  eval = elem

  quote⊣eval
    : ∀ (c : Con CP) (x : StablePoint)
    → _⊑_ CP (normalize c) (eval x) ↔ _⊑_ CP c (eval x)
  quote⊣eval = Ref.quot⊣evalm GC

-- Kernel-level derived infrastructure (the “tooling loop” vocabulary).
module OnKernel
  {ℓ ℓRel ℓCode : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (E : Effectivity (bnd K))
  where
  open Effectivity E using (GC)

  -- Effective kernel (reflected observation).
  Kᵉᶠᶠ : Kernel ℓ ℓRel ℓCode
  Kᵉᶠᶠ = Eff.effectiveKernel K GC

  effectivise : KernelHom K Kᵉᶠᶠ
  effectivise = Eff.effectivise K GC

  effectiviseFlow : KernelHomFlow GC GC effectivise
  effectiviseFlow = Eff.effectiviseFlow K GC

  -- Stable completion (canonical quotation target).
  quoteKernel : Kernel _ _ _
  quoteKernel = Quote.quoteKernel GC

  stableCompletion : KernelHom K quoteKernel
  stableCompletion = StableComp.stableCompletion K GC

  stableCompletionFlow : KernelHomFlow GC GC stableCompletion
  stableCompletionFlow = StableComp.stableCompletionFlow K GC

  -- Effective observation and packets.
  effObs : Code K → Con (bnd K)
  effObs = Pack.effObs {K = K} GC

  Packet : Code K → Code K → Set ℓRel
  Packet = Pack.Packet {K = K} GC

  EffectiveCodePreorder : ConPreorder ℓCode ℓRel
  EffectiveCodePreorder = Pack.EffectiveCodePreorder K GC

-- Effectivity induced by an adjunction/residual (Galois connection).
effectivityFromGalois
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → Gal.GaloisConnection A B
  → Effectivity A
effectivityFromGalois G =
  record { GC = Gal.closure G }

effectivityFromGalois-rightImageStable
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : Gal.GaloisConnection A B)
  → Con B
  → Effectivity.StablePoint (effectivityFromGalois G)
effectivityFromGalois-rightImageStable G =
  Gal.rightImageStable G

effectivityFromGalois-stableReflectiveImage
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : Gal.GaloisConnection A B)
  → (x : Effectivity.StablePoint (effectivityFromGalois G))
  → Gal.RightImagePoint G (elem x)
effectivityFromGalois-stableReflectiveImage G x =
  Gal.stableReflectiveImage G x

effectivityFromGalois-stableRepresentation
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : Gal.GaloisConnection A B)
  → (x : Effectivity.StablePoint (effectivityFromGalois G))
  → Σ (Con B) (λ b → _≈_ A (elem x) (Gal.R G b))
effectivityFromGalois-stableRepresentation G x =
  effectivityFromGalois-stableReflectiveImage G x
