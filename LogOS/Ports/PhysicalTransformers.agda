{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PhysicalTransformers where

-- Dependent-locality tooling for shared distributed semantics.
--
-- This is the dependent-locality variant of the shared distributed-semantics
-- tooling:
-- the shared boundary is `LocalBoundary I O`, where the observable
-- interface preorder `O i` may vary with the locality index `i`.
--
-- The key tooling loop theorem has the following shape:
-- if a boundary translation is pointwise and each local component preserves the
-- local doctrine, then the induced boundary-wide translation preserves the
-- dependent pointwise doctrine.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap; ≡→≈)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.LT.Kernel using (decode)
open import LogOS.Ports.Locality.Core using
  ( LocalityPort
  ; localKernel
  ; LocalBoundary
  )
open import LogOS.Ports.Locality.Lifts using (pointwiseClosure)

-- --------------------------------------------------------------------------
-- Pointwise (locality-preserving) boundary maps.

pointwiseMap
  : ∀ {ℓI ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {I : Set ℓI}
    {O₁ : I → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : I → ConPreorder ℓOCon₂ ℓORel₂}
  → ((i : I) → Con (O₁ i) → Con (O₂ i))
  → Con (LocalBoundary I O₁) → Con (LocalBoundary I O₂)
pointwiseMap mapAt F i = mapAt i (F i)

pointwiseMap-mono
  : ∀ {ℓI ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {I : Set ℓI}
    {O₁ : I → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : I → ConPreorder ℓOCon₂ ℓORel₂}
    (mapAt : (i : I) → Con (O₁ i) → Con (O₂ i))
  → (∀ i → MonoMap (O₁ i) (O₂ i) (mapAt i))
  → MonoMap
      (LocalBoundary I O₁)
      (LocalBoundary I O₂)
      (pointwiseMap {O₁ = O₁} {O₂ = O₂} mapAt)
pointwiseMap-mono mapAt monoAt FG i = monoAt i (FG i)

-- Convenience alias: the “endomap” (same local languages) is the same combinator.
pointwiseEndoMap
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → Con (O i) → Con (O i))
  → Con (LocalBoundary I O) → Con (LocalBoundary I O)
pointwiseEndoMap {I = I} {O = O} =
  pointwiseMap {I = I} {O₁ = O} {O₂ = O}

pointwiseEndoMap-mono
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    (mapAt : (i : I) → Con (O i) → Con (O i))
  → (∀ i → MonoMap (O i) (O i) (mapAt i))
  → MonoMap
      (LocalBoundary I O)
      (LocalBoundary I O)
      (pointwiseEndoMap {I = I} {O = O} mapAt)
pointwiseEndoMap-mono mapAt monoAt FG i = monoAt i (FG i)

-- --------------------------------------------------------------------------
-- Tooling loop theorem:
-- local (per-index) flow preservation implies boundary-wide flow preservation.
--
-- A physics-style reading is optional. The mechanised content is
-- locality-indexed boundary transport plus closure preservation.

pointwiseMap-preservesFlow
  : ∀ {ℓI ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {I : Set ℓI}
    {O₁ : I → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : I → ConPreorder ℓOCon₂ ℓORel₂}
    (GC₀₁ : (i : I) → GuardedClosure (O₁ i))
    (GC₀₂ : (i : I) → GuardedClosure (O₂ i))
    (mapAt : (i : I) → Con (O₁ i) → Con (O₂ i))
  → (∀ i c → _⊑_ (O₂ i) (mapAt i (Flow (GC₀₁ i) c)) (Flow (GC₀₂ i) (mapAt i c)))
  → ∀ c
    → _⊑_ (LocalBoundary I O₂)
        (pointwiseMap {I = I} {O₁ = O₁} {O₂ = O₂} mapAt
          (Flow (pointwiseClosure {I = I} {O = O₁} GC₀₁) c))
        (Flow (pointwiseClosure {I = I} {O = O₂} GC₀₂)
          (pointwiseMap {I = I} {O₁ = O₁} {O₂ = O₂} mapAt c))
pointwiseMap-preservesFlow GC₀₁ GC₀₂ mapAt causalAt c i = causalAt i (c i)

pointwiseEndoMap-preservesFlow
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    (GC₀ : (i : I) → GuardedClosure (O i))
    (mapAt : (i : I) → Con (O i) → Con (O i))
  → (∀ i c → _⊑_ (O i) (mapAt i (Flow (GC₀ i) c)) (Flow (GC₀ i) (mapAt i c)))
  → ∀ c
    → _⊑_ (LocalBoundary I O)
        (pointwiseEndoMap {I = I} {O = O} mapAt
          (Flow (pointwiseClosure {I = I} {O = O} GC₀) c))
        (Flow (pointwiseClosure {I = I} {O = O} GC₀)
          (pointwiseEndoMap {I = I} {O = O} mapAt c))
pointwiseEndoMap-preservesFlow {I = I} {O = O} GC₀ mapAt causalAt =
  pointwiseMap-preservesFlow {I = I} {O₁ = O} {O₂ = O} GC₀ GC₀ mapAt causalAt

-- --------------------------------------------------------------------------
-- Certified adapters: first assemble the pointwise kernel morphism itself,
-- then add the flow-preservation certificate when needed.

mkKernelHomPointwise₂
  : ∀ {ℓCode ℓI ℓOCon ℓORel}
    {X : Set ℓCode}
    {Y : Set ℓCode}
    {I : Set ℓI}
    {O₁ : I → ConPreorder ℓOCon ℓORel}
    {O₂ : I → ConPreorder ℓOCon ℓORel}
  → (P₁ : LocalityPort X I O₁)
  → (P₂ : LocalityPort Y I O₂)
  → (mapAt : (i : I) → Con (O₁ i) → Con (O₂ i))
  → (monoAt : ∀ i → MonoMap (O₁ i) (O₂ i) (mapAt i))
  → (mapCode : X → Y)
  → (decode-mapCode
      : ∀ γ
      → _≈_ (LocalBoundary I O₂)
          (decode (localKernel P₂) (mapCode γ))
          (pointwiseMap {I = I} {O₁ = O₁} {O₂ = O₂} mapAt
            (decode (localKernel P₁) γ)))
  → KernelHom (localKernel P₁) (localKernel P₂)
mkKernelHomPointwise₂ {I = I} {O₁ = O₁} {O₂ = O₂} P₁ P₂ mapAt monoAt mapCode decode-mapCode =
  mkKernelHomParts
    (record
      { map∂ = pointwiseMap {I = I} {O₁ = O₁} {O₂ = O₂} mapAt
      ; map∂-mono =
          pointwiseMap-mono {I = I} {O₁ = O₁} {O₂ = O₂} mapAt monoAt
      })
    (record
      { mapCode = mapCode
      ; decode-mapCode = decode-mapCode
      })

mkKernelHomPointwise
  : ∀ {ℓCode ℓI ℓOCon ℓORel}
    {X Y : Set ℓCode}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → (P  : LocalityPort X I O)
  → (P' : LocalityPort Y I O)
  → (mapAt : (i : I) → Con (O i) → Con (O i))
  → (monoAt : ∀ i → MonoMap (O i) (O i) (mapAt i))
  → (mapCode : X → Y)
  → (decode-mapCode
      : ∀ γ
      → _≈_ (LocalBoundary I O)
          (decode (localKernel P') (mapCode γ))
          (pointwiseEndoMap {I = I} {O = O} mapAt
            (decode (localKernel P) γ)))
  → KernelHom (localKernel P) (localKernel P')
mkKernelHomPointwise {I = I} {O = O} P P' mapAt monoAt mapCode decode-mapCode =
  mkKernelHomPointwise₂
    {I = I} {O₁ = O} {O₂ = O}
    P P'
    mapAt
    monoAt
    mapCode
    decode-mapCode

mkKernelHomFlow₂
  : ∀ {ℓCode ℓI ℓOCon ℓORel}
    {X : Set ℓCode}
    {Y : Set ℓCode}
    {I : Set ℓI}
    {O₁ : I → ConPreorder ℓOCon ℓORel}
    {O₂ : I → ConPreorder ℓOCon ℓORel}
  → (GC₀₁ : (i : I) → GuardedClosure (O₁ i))
  → (GC₀₂ : (i : I) → GuardedClosure (O₂ i))
  → (P₁ : LocalityPort X I O₁)
  → (P₂ : LocalityPort Y I O₂)
  → (mapAt : (i : I) → Con (O₁ i) → Con (O₂ i))
  → (monoAt : ∀ i → MonoMap (O₁ i) (O₂ i) (mapAt i))
  → (causalAt : ∀ i c → _⊑_ (O₂ i) (mapAt i (Flow (GC₀₁ i) c)) (Flow (GC₀₂ i) (mapAt i c)))
  → (mapCode : X → Y)
  → (decode-mapCode
      : ∀ γ
      → _≈_ (LocalBoundary I O₂)
          (decode (localKernel P₂) (mapCode γ))
          (pointwiseMap {I = I} {O₁ = O₁} {O₂ = O₂} mapAt
            (decode (localKernel P₁) γ)))
  → Σ
      (KernelHom (localKernel P₁) (localKernel P₂))
      (λ h → KernelHomFlow
        (pointwiseClosure {I = I} {O = O₁} GC₀₁)
        (pointwiseClosure {I = I} {O = O₂} GC₀₂)
        h)
mkKernelHomFlow₂ {I = I} {O₁ = O₁} {O₂ = O₂} GC₀₁ GC₀₂ P₁ P₂ mapAt monoAt causalAt mapCode decode-mapCode =
  h , hf
  where
    h : KernelHom (localKernel P₁) (localKernel P₂)
    h = mkKernelHomPointwise₂ P₁ P₂ mapAt monoAt mapCode decode-mapCode

    hf : KernelHomFlow
          (pointwiseClosure {I = I} {O = O₁} GC₀₁)
          (pointwiseClosure {I = I} {O = O₂} GC₀₂)
          h
    hf =
      record
        { preserves-Flow =
            pointwiseMap-preservesFlow {I = I} {O₁ = O₁} {O₂ = O₂} GC₀₁ GC₀₂ mapAt causalAt
        }

mkKernelHomFlow
  : ∀ {ℓCode ℓI ℓOCon ℓORel}
    {X Y : Set ℓCode}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → (GC₀ : (i : I) → GuardedClosure (O i))
  → (P  : LocalityPort X I O)
  → (P' : LocalityPort Y I O)
  → (mapAt : (i : I) → Con (O i) → Con (O i))
  → (monoAt : ∀ i → MonoMap (O i) (O i) (mapAt i))
  → (causalAt : ∀ i c → _⊑_ (O i) (mapAt i (Flow (GC₀ i) c)) (Flow (GC₀ i) (mapAt i c)))
  → (mapCode : X → Y)
  → (decode-mapCode
      : ∀ γ
      → _≈_ (LocalBoundary I O)
          (decode (localKernel P') (mapCode γ))
          (pointwiseEndoMap {I = I} {O = O} mapAt
            (decode (localKernel P) γ)))
  → Σ
      (KernelHom (localKernel P) (localKernel P'))
      (λ h → KernelHomFlow
        (pointwiseClosure {I = I} {O = O} GC₀)
        (pointwiseClosure {I = I} {O = O} GC₀)
        h)
mkKernelHomFlow {I = I} {O = O} GC₀ P P' mapAt monoAt causalAt mapCode decode-mapCode =
  mkKernelHomFlow₂
    {I = I} {O₁ = O} {O₂ = O}
    GC₀ GC₀
    P P'
    mapAt
    monoAt
    causalAt
    mapCode
    decode-mapCode

private
  mkKernelHomFlow₂-base = mkKernelHomFlow₂

-- Strict-input wrappers: allow supplying definitional decode coherence and
-- recover the default ≈-coherent constructors by lifting `≡` to `≈`.
module Strict where
  mkKernelHomFlow₂≡
    : ∀ {ℓCode ℓI ℓOCon ℓORel}
      {X : Set ℓCode}
      {Y : Set ℓCode}
      {I : Set ℓI}
      {O₁ : I → ConPreorder ℓOCon ℓORel}
      {O₂ : I → ConPreorder ℓOCon ℓORel}
    → (GC₀₁ : (i : I) → GuardedClosure (O₁ i))
    → (GC₀₂ : (i : I) → GuardedClosure (O₂ i))
    → (P₁ : LocalityPort X I O₁)
    → (P₂ : LocalityPort Y I O₂)
    → (mapAt : (i : I) → Con (O₁ i) → Con (O₂ i))
    → (monoAt : ∀ i → MonoMap (O₁ i) (O₂ i) (mapAt i))
    → (causalAt : ∀ i c → _⊑_ (O₂ i) (mapAt i (Flow (GC₀₁ i) c)) (Flow (GC₀₂ i) (mapAt i c)))
    → (mapCode : X → Y)
    → (decode-mapCode
        : ∀ γ
        → decode (localKernel P₂) (mapCode γ)
          ≡
          pointwiseMap {I = I} {O₁ = O₁} {O₂ = O₂} mapAt
            (decode (localKernel P₁) γ))
    → Σ
        (KernelHom (localKernel P₁) (localKernel P₂))
        (λ h → KernelHomFlow
          (pointwiseClosure {I = I} {O = O₁} GC₀₁)
          (pointwiseClosure {I = I} {O = O₂} GC₀₂)
          h)
  mkKernelHomFlow₂≡ {I = I} {O₁ = O₁} {O₂ = O₂} GC₀₁ GC₀₂ P₁ P₂ mapAt monoAt causalAt mapCode decode-mapCode =
    mkKernelHomFlow₂-base
      {I = I} {O₁ = O₁} {O₂ = O₂}
      GC₀₁ GC₀₂
      P₁ P₂
      mapAt
      monoAt
      causalAt
      mapCode
      (λ γ → ≡→≈ {CP = LocalBoundary I O₂} (decode-mapCode γ))

  mkKernelHomFlow≡
    : ∀ {ℓCode ℓI ℓOCon ℓORel}
      {X Y : Set ℓCode}
      {I : Set ℓI}
      {O : I → ConPreorder ℓOCon ℓORel}
    → (GC₀ : (i : I) → GuardedClosure (O i))
    → (P  : LocalityPort X I O)
    → (P' : LocalityPort Y I O)
    → (mapAt : (i : I) → Con (O i) → Con (O i))
    → (monoAt : ∀ i → MonoMap (O i) (O i) (mapAt i))
    → (causalAt : ∀ i c → _⊑_ (O i) (mapAt i (Flow (GC₀ i) c)) (Flow (GC₀ i) (mapAt i c)))
    → (mapCode : X → Y)
    → (decode-mapCode
        : ∀ γ
        → decode (localKernel P') (mapCode γ)
          ≡
          pointwiseEndoMap {I = I} {O = O} mapAt
            (decode (localKernel P) γ))
    → Σ
        (KernelHom (localKernel P) (localKernel P'))
        (λ h → KernelHomFlow
          (pointwiseClosure {I = I} {O = O} GC₀)
          (pointwiseClosure {I = I} {O = O} GC₀)
          h)
  mkKernelHomFlow≡ {I = I} {O = O} GC₀ P P' mapAt monoAt causalAt mapCode decode-mapCode =
    mkKernelHomFlow₂≡
      {I = I} {O₁ = O} {O₂ = O}
      GC₀ GC₀
      P P'
      mapAt
      monoAt
      causalAt
      mapCode
      decode-mapCode
