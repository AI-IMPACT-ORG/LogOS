{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.EffectivePackets where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Effective semantics and “packetisation” as boundary closure.
--
-- This module is the kernel-native core of the “non-abelian scaling” pattern:
--
--   effObs  = Flow ∘ decode
--
-- and the induced effective/packet equivalence:
--
--   γ and δ are in the same packet  :⇔  effObs γ ≈ effObs δ
--
-- The key transport fact is the tooling loop:
-- flow-preserving adapters commute with normalisation up to refinement.
-- Public theorem surfaces use `≼` as the order-flavoured presentation alias.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.View using (View; PullbackPreorder; _≈[_]_)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; mapCode)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.LT.Theorems.Effectivisation using
    ( effectiveKernel
    ; normalize-decode-mapCode
    )

-- --------------------------------------------------------------------------
-- Effective observation and packet equivalence.

effObs
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → GuardedClosure (bnd K)
  → Code K → Con (bnd K)
effObs {K = K} GC γ = decode (effectiveKernel K GC) γ

effectiveView
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → View (Code K) (bnd K)
effectiveView {K = K} GC = record { μ = effObs {K = K} GC }

Packet
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → Code K → Code K → Set ℓRel
Packet {K = K} GC γ δ = γ ≈[ effectiveView {K = K} GC ] δ

EffectiveCodePreorder
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
  → GuardedClosure (bnd K)
  → ConPreorder ℓCode ℓRel
EffectiveCodePreorder K GC = PullbackPreorder (effectiveView {K = K} GC)

-- --------------------------------------------------------------------------
-- Tooling loop: effectivisation transports across flow-preserving adapters.

effObs-transport
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (GC : GuardedClosure (bnd K))
    (GC' : GuardedClosure (bnd K'))
    (h : KernelHom K K')
  → KernelHomFlow GC GC' h
  → ∀ γ
  → _≼_ (bnd K')
      (map∂ h (effObs {K = K} GC γ))
      (effObs {K = K'} GC' (mapCode h γ))
effObs-transport {K = K} {K' = K'} GC GC' h HF γ =
  normalize-decode-mapCode {K = K} {K' = K'} GC GC' h HF γ
