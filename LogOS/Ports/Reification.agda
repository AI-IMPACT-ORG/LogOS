{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Reification where

-- The “logical quine” step, packaged as pristine LogOS architecture.
--
--   Flow (a guarded closure) gives effectivisation (reflected observation);
--   effectivisation plus quotation gives safe self-reference.
--
-- Concretely, given a boundary preorder `CP` and a closure `GC : GuardedClosure CP`,
-- we get a canonical factorisation:
--
--   boundary-as-code  --(unroll/Flow)-->  effective boundary-as-code
--                  --(quote/reify)-->     stable-points kernel
--
-- The composite is a kernel morphism (refinement-first; `≈`-coherent) that satisfies:
--
--   decode ∘ mapCode  ≈  Flow ∘ decode
--
-- This is the “quine feeling”: the boundary can reify (quote) its own effective
-- constraints as code, but only up to `Flow` (the safety valve).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Effectivity using (Effectivity)
open import LogOS.LT.Hom.Core using (KernelHom)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.LT.Kernel using (BoundaryKernel)
open import LogOS.LT.LOG.ArchitectureQuote2Cat using (quoteKernel; quotePort; QuotePort)
open import LogOS.LT.Theorems.Effectivisation using (effectiveKernel)
open import LogOS.LT.Theorems.StableCompletion using
  ( quoteStableHom
  ; quoteStableHomFlow
  ; stableCompletion
  ; stableCompletionFlow
  )

-- Second step of the factorisation: from reflected observation to stable code.
--
-- Boundary map is identity; code map is the stable-point reflector `quot`.
reifyStable
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → KernelHom
      (effectiveKernel (BoundaryKernel CP) GC)
      (quoteKernel GC)
reifyStable {CP = CP} GC = quoteStableHom (BoundaryKernel CP) GC

reifyStableFlow
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → KernelHomFlow GC GC (reifyStable {CP = CP} GC)
reifyStableFlow {CP = CP} GC = quoteStableHomFlow (BoundaryKernel CP) GC

-- The composite “quine morphism”: boundary quotes itself up to Flow.
quoteHom
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → KernelHom (BoundaryKernel CP) (quoteKernel GC)
quoteHom {CP = CP} GC = stableCompletion (BoundaryKernel CP) GC

quoteHomFlow
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → KernelHomFlow GC GC (quoteHom {CP = CP} GC)
quoteHomFlow {CP = CP} GC = stableCompletionFlow (BoundaryKernel CP) GC

-- Canonical QuotePort on the closure kernel (no extra structure required).
quoteQP
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → QuotePort (quoteKernel GC)
quoteQP = quotePort

-- Convenience: take effectivity records directly (dependency injection).
reifyStableᵉ
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (E : Effectivity CP)
  → KernelHom
      (effectiveKernel (BoundaryKernel CP) (Effectivity.GC E))
      (quoteKernel (Effectivity.GC E))
reifyStableᵉ E = reifyStable (Effectivity.GC E)

quoteHomᵉ
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (E : Effectivity CP)
  → KernelHom (BoundaryKernel CP) (quoteKernel (Effectivity.GC E))
quoteHomᵉ E = quoteHom (Effectivity.GC E)

quoteHomFlowᵉ
  : ∀ {ℓCon ℓRel : Level}
    {CP : ConPreorder ℓCon ℓRel}
  → (E : Effectivity CP)
  → KernelHomFlow (Effectivity.GC E) (Effectivity.GC E) (quoteHomᵉ E)
quoteHomFlowᵉ E = quoteHomFlow (Effectivity.GC E)
