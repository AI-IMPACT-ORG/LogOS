{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.StableCompletion where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Stable completion / canonical quotation target for any kernel.
--
-- Given a kernel `K` and a guarded closure `GC` on its boundary, there is a
-- canonical “completion” of `K` into the stable-points (quote) kernel
-- `quoteKernel GC`.
--
-- Architecturally this is a quine-shaped factorisation:
--
--   K  --(effectivise/Flow)-->  Kᵉᶠᶠ  --(quot)-->  quoteKernel GC
--
-- The crucial law is judgmentally equal after unfolding, hence `≈` by reflexivity:
--
--   decode (mapCode γ)  ≈  Flow (decode γ)
--
-- This is the kernel-native form of “partial self-reference”: you can always
-- reify a model into stable points, but only through the safety valve `Flow`.
--
-- Pedantic note (what “canonical” means here):
-- the quine law determines the completed adapter *up to observation* (pointwise `≈`).
-- See `CompletionLaw` / `completion-noFork` below.
--
-- Public-facing note:
-- the completion-order statements below use `≼` as an order-flavoured alias
-- for the underlying boundary refinement relation.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; idMonoMap; refl⊑)
open import LogOS.LT.Coherence using (CohLevel; CohMode; CohRel; approx; under)
private
  module CPReasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts; map∂; map∂-mono; mapCode; decode-mapCode; _∘_; _⇒_)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.LT.Reflection using (quot)
open import LogOS.LT.LOG.ArchitectureQuote2Cat using (quoteKernel)
open import LogOS.LT.Theorems.Effectivisation using (effectiveKernel; effectivise; effectiviseFlow)

-- Step 2: from the effective kernel into stable points.
--
-- Boundary map is identity; the code map is the stable-point reflector `quot`
-- applied to the effective observation.
quoteStableHom
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHom
      (effectiveKernel K GC)
      (quoteKernel GC)
quoteStableHom K GC =
  mkKernelHomParts
    (record
      { map∂ = λ c → c
      ; map∂-mono = idMonoMap {CP = bnd K}
      })
    (record
      { mapCode = λ γ → quot GC (decode K γ)
      ; decode-mapCode = λ γ → refl⊑ (bnd K) , refl⊑ (bnd K)
      })

quoteStableHomFlow
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHomFlow GC GC (quoteStableHom K GC)
quoteStableHomFlow K GC =
  record { preserves-Flow = λ _ → refl⊑ (bnd K) }

-- The composite stable completion: any kernel canonically factors through stable points.
stableCompletion
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHom K (quoteKernel GC)
stableCompletion K GC =
  quoteStableHom K GC ∘ effectivise K GC

stableCompletionFlow
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHomFlow GC GC (stableCompletion K GC)
stableCompletionFlow K GC =
  composeKernelHomFlow
    (effectiviseFlow K GC)
    (quoteStableHomFlow K GC)
  where
    open import LogOS.LT.HomFlow using (composeKernelHomFlow)

stableCompletion-law
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → ∀ γ
  → CohRel m (bnd K)
      (decode (quoteKernel GC) (mapCode (stableCompletion K GC) γ))
      (Flow GC (decode K γ))
stableCompletion-law {m = approx} K GC γ =
  (refl⊑ (bnd K) , refl⊑ (bnd K))
stableCompletion-law {m = under} K GC γ =
  refl⊑ (bnd K)

-- --------------------------------------------------------------------------
-- “Canonical means forced”: uniqueness up to observation.
--
-- There can be many Agda-level inhabitants of `Stable` with the same `elem`
-- (different stability witnesses), so we do not claim propositional equality
-- of completed code maps. What *is* forced is the observed meaning:
-- decoding the completed code is normalisation.

record CompletionLawLike
  (m : CohMode)
  {ℓ ℓRel ℓCode : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (GC : GuardedClosure (bnd K))
  (h : KernelHom K (quoteKernel GC))
  : Set (ℓCode ⊔ CohLevel m ℓ ℓRel)
  where
  field
    decodeCohFlow : ∀ γ
      → CohRel m (bnd K)
          (decode (quoteKernel GC) (mapCode h γ))
          (Flow GC (decode K γ))

open CompletionLawLike public

CompletionLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
    (h : KernelHom K (quoteKernel GC))
  → Set (ℓCode ⊔ ℓRel)
CompletionLaw = CompletionLawLike approx

CompletionLaw≈
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {GC : GuardedClosure (bnd K)}
    {h : KernelHom K (quoteKernel GC)}
  → CompletionLaw K GC h
  → ∀ γ
  → _≈_ (bnd K)
      (decode (quoteKernel GC) (mapCode h γ))
      (Flow GC (decode K γ))
CompletionLaw≈ law γ = decodeCohFlow law γ

stableCompletionCompletionLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → CompletionLaw K GC (stableCompletion K GC)
stableCompletionCompletionLaw K GC =
  record
    { decodeCohFlow = stableCompletion-law {m = approx} K GC
    }

private
  decode⊑Flow
    : ∀ {ℓ ℓRel ℓCode : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {GC : GuardedClosure (bnd K)}
      {h : KernelHom K (quoteKernel GC)}
    → CompletionLaw K GC h
    → ∀ γ
    → _≼_ (bnd K)
        (decode (quoteKernel GC) (mapCode h γ))
        (Flow GC (decode K γ))
  decode⊑Flow law γ = fst (decodeCohFlow law γ)

  Flow⊑decode
    : ∀ {ℓ ℓRel ℓCode : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {GC : GuardedClosure (bnd K)}
      {h : KernelHom K (quoteKernel GC)}
    → CompletionLaw K GC h
    → ∀ γ
    → _≼_ (bnd K)
        (Flow GC (decode K γ))
        (decode (quoteKernel GC) (mapCode h γ))
  Flow⊑decode law γ = snd (decodeCohFlow law γ)

completion-map∂-forcedOnDecode
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
    (h : KernelHom K (quoteKernel GC))
  → CompletionLaw K GC h
  → ∀ γ
  → _≈_ (bnd K)
      (map∂ h (decode K γ))
      (Flow GC (decode K γ))
completion-map∂-forcedOnDecode K GC h law γ =
  ( forward , backward )
  where
    CP = bnd K
    module R = CPReasoning CP
    open R using (begin≼_; _≼⟨_⟩_; _∎≼)

    forward : _≼_ CP (map∂ h (decode K γ)) (Flow GC (decode K γ))
    forward =
      begin≼
        map∂ h (decode K γ)
          ≼⟨ snd (decode-mapCode h γ) ⟩
        decode (quoteKernel GC) (mapCode h γ)
          ≼⟨ decode⊑Flow law γ ⟩
        Flow GC (decode K γ) ∎≼

    backward : _≼_ CP (Flow GC (decode K γ)) (map∂ h (decode K γ))
    backward =
      begin≼
        Flow GC (decode K γ)
          ≼⟨ Flow⊑decode law γ ⟩
        decode (quoteKernel GC) (mapCode h γ)
          ≼⟨ fst (decode-mapCode h γ) ⟩
        map∂ h (decode K γ) ∎≼

-- Any two completions satisfying the quine law are equal up to observation
-- (pointwise `≈`, hence by definition of `_⇒∂_` the 1-cells mutually refine in `LOG`).
completion-noFork
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
    (h₁ h₂ : KernelHom K (quoteKernel GC))
  → CompletionLaw K GC h₁
  → CompletionLaw K GC h₂
  → ∀ γ
  → _≈_ (bnd K)
      (decode (quoteKernel GC) (mapCode h₁ γ))
      (decode (quoteKernel GC) (mapCode h₂ γ))
completion-noFork K GC h₁ h₂ law₁ law₂ γ =
  ( forward , backward )
  where
    CP = bnd K
    module R = CPReasoning CP
    open R using (begin≼_; _≼⟨_⟩_; _∎≼)

    forward
      : _≼_ CP
          (decode (quoteKernel GC) (mapCode h₁ γ))
          (decode (quoteKernel GC) (mapCode h₂ γ))
    forward =
      begin≼
        decode (quoteKernel GC) (mapCode h₁ γ) ≼⟨ decode⊑Flow law₁ γ ⟩
        Flow GC (decode K γ) ≼⟨ Flow⊑decode law₂ γ ⟩
        decode (quoteKernel GC) (mapCode h₂ γ) ∎≼

    backward
      : _≼_ CP
          (decode (quoteKernel GC) (mapCode h₂ γ))
          (decode (quoteKernel GC) (mapCode h₁ γ))
    backward =
      begin≼
        decode (quoteKernel GC) (mapCode h₂ γ) ≼⟨ decode⊑Flow law₂ γ ⟩
        Flow GC (decode K γ) ≼⟨ Flow⊑decode law₁ γ ⟩
        decode (quoteKernel GC) (mapCode h₁ γ) ∎≼

-- Specialisation: `stableCompletion` is the canonical completion, and any other
-- completion is observationally equal to it.
stableCompletion-noFork
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
    (h : KernelHom K (quoteKernel GC))
  → CompletionLaw K GC h
  → ∀ γ
  → _≈_ (bnd K)
      (decode (quoteKernel GC) (mapCode (stableCompletion K GC) γ))
      (decode (quoteKernel GC) (mapCode h γ))
stableCompletion-noFork K GC h law γ =
  completion-noFork
    K
    GC
    (stableCompletion K GC)
    h
    (stableCompletionCompletionLaw K GC)
    law
    γ

stableCompletion⇒completion
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
    (h : KernelHom K (quoteKernel GC))
  → CompletionLaw K GC h
  → stableCompletion K GC ⇒ h
stableCompletion⇒completion K GC h law γ =
  let
    module R = CPReasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    decode (quoteKernel GC) (mapCode (stableCompletion K GC) γ)
      ⊑⟨ decode⊑Flow (stableCompletionCompletionLaw K GC) γ ⟩
    Flow GC (decode K γ) ⊑⟨ Flow⊑decode law γ ⟩
    decode (quoteKernel GC) (mapCode h γ) ∎⊑

completion⇒stableCompletion
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
    (h : KernelHom K (quoteKernel GC))
  → CompletionLaw K GC h
  → h ⇒ stableCompletion K GC
completion⇒stableCompletion K GC h law γ =
  let
    module R = CPReasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    decode (quoteKernel GC) (mapCode h γ) ⊑⟨ decode⊑Flow law γ ⟩
    Flow GC (decode K γ) ⊑⟨ Flow⊑decode (stableCompletionCompletionLaw K GC) γ ⟩
    decode (quoteKernel GC) (mapCode (stableCompletion K GC) γ) ∎⊑
