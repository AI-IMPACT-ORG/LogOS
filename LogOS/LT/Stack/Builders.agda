{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Builders where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Canonical stack-map builders.
--
-- This module owns the generic "assemble a stack map from its boundary/code
-- parts" combinators. Higher-level shells such as `LogOS.LT.TypeTheory.Stack`
-- only re-export these deep constructions.

open import LogOS.Prelude
open import LogOS.LT.Coherence using (CohMode; CohRel; approx; under)
open import LogOS.LT.ConPreorder using (Con; MonoMap)
open import LogOS.LT.Kernel using (Kernel; Code; bnd; decode)
open import LogOS.LT.View using (μ)
import LogOS.LT.Hom.Core as Hom
import LogOS.LT.Stack.Core as Stack

StackDecodeLaw
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → Set _
StackDecodeLaw {m = m} {S = S} {K' = K'} map∂ mapCode =
  ∀ o γ
  → CohRel m (bnd K') (decode K' (mapCode o γ)) (map∂ (μ (Stack.op S o) γ))

mkStackMapLike
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (map∂-mono : MonoMap (Stack.bnd S) (Kernel.bnd K') map∂)
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → StackDecodeLaw {m = m} {S = S} {K' = K'} map∂ mapCode
  → Stack.StackMapLike {m = m} S K'
mkStackMapLike map∂′ map∂-mono′ mapCode′ decode-mapCode′ =
  record
    { map∂ = map∂′
    ; map∂-mono = map∂-mono′
    ; mapCode = mapCode′
    ; decode-mapCode = decode-mapCode′
    }

mkStackMap
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (map∂-mono : MonoMap (Stack.bnd S) (Kernel.bnd K') map∂)
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → StackDecodeLaw {m = approx} {S = S} {K' = K'} map∂ mapCode
  → Stack.StackMap S K'
mkStackMap = mkStackMapLike {m = approx}

mkStackMap⊑
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (map∂-mono : MonoMap (Stack.bnd S) (Kernel.bnd K') map∂)
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → StackDecodeLaw {m = under} {S = S} {K' = K'} map∂ mapCode
  → Stack.StackMap⊑ S K'
mkStackMap⊑ = mkStackMapLike {m = under}

mkStackKernelHomLike
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (map∂-mono : MonoMap (Stack.bnd S) (Kernel.bnd K') map∂)
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → StackDecodeLaw {m = m} {S = S} {K' = K'} map∂ mapCode
  → Hom.KernelHomLike m (Stack.stackKernel S) K'
mkStackKernelHomLike {m = m} map∂′ map∂-mono′ mapCode′ decode-mapCode′ =
  Stack.toKernelHomLike (mkStackMapLike {m = m} map∂′ map∂-mono′ mapCode′ decode-mapCode′)

mkStackKernelHom
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (map∂-mono : MonoMap (Stack.bnd S) (Kernel.bnd K') map∂)
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → StackDecodeLaw {m = approx} {S = S} {K' = K'} map∂ mapCode
  → Hom.KernelHom (Stack.stackKernel S) K'
mkStackKernelHom = mkStackKernelHomLike {m = approx}

mkStackKernelHom⊑
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
  → (map∂ : Con (Stack.bnd S) → Con (Kernel.bnd K'))
  → (map∂-mono : MonoMap (Stack.bnd S) (Kernel.bnd K') map∂)
  → (mapCode : ∀ o → Stack.Code S o → Code K')
  → StackDecodeLaw {m = under} {S = S} {K' = K'} map∂ mapCode
  → Hom.KernelHom⊑ (Stack.stackKernel S) K'
mkStackKernelHom⊑ = mkStackKernelHomLike {m = under}

mapCodeFrom
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
    {o : Stack.Op S}
  → Hom.KernelHom (Stack.opKernel S o) K'
  → Stack.Code S o
  → Code K'
mapCodeFrom h γ = Hom.mapCode h γ
