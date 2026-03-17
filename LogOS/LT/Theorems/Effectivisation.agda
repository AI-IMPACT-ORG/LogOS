{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.Effectivisation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Effectivisation / unrolling spine for Flow-based architectures.
--
-- Given a guarded closure `GC` on a kernel boundary, we can refine any kernel by
-- reflecting its observation through `Flow`:
--
--   decodeᵉᶠᶠ  ≔  Flow GC ∘ decode
--
-- This produces a new kernel at the *same* code universe (no extra axioms),
-- together with a canonical adapter and the central tooling loop:
-- flow-preserving adapters commute with effectivisation up to refinement.
--
-- Public-facing note:
-- the transport theorems below use `≼` as an order-flavoured alias for that
-- same refinement relation.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.LT.ConPreorder using (_⊑_; _≈_; refl⊑; ≈-refl)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts; map∂; map∂-mono; mapCode; decode-mapCode)
open import LogOS.LT.HomFlow using (KernelHomFlow; preserves-Flow)

-- --------------------------------------------------------------------------
-- Effective kernel: same code, refined observation.

effectiveKernel
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K  : Kernel ℓ ℓRel ℓCode)
  → GuardedClosure (bnd K)
  → Kernel ℓ ℓRel ℓCode
effectiveKernel K GC =
  record
    { bnd = bnd K
    ; Code = Code K
    ; decode = λ γ → Flow GC (decode K γ)
    }

-- Iterated effectivisation is literally composition of the chosen closures:
-- decoding in `((Kᵉᶠᶠ under GC)ᵉᶠᶠ under GC')` refines to (and is refined by)
-- `Flow GC' ∘ Flow GC ∘ decode`.
decode-effectiveKernel²≈
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC  : GuardedClosure (bnd K))
    (GC' : GuardedClosure (bnd K))
  → ∀ γ
  → _≈_ (bnd K)
      (decode (effectiveKernel (effectiveKernel K GC) GC') γ)
      (Flow GC' (Flow GC (decode K γ)))
decode-effectiveKernel²≈ K GC GC' γ =
  ≈-refl (bnd K) (Flow GC' (Flow GC (decode K γ)))

-- Canonical adapter K → Kᵉᶠᶠ (the “effectivisation map”).
effectivise
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K  : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHom K (effectiveKernel K GC)
effectivise K GC =
  mkKernelHomParts
    (record
      { map∂ = Flow GC
      ; map∂-mono = GuardedClosure.mono GC
      })
    (record
      { mapCode = λ γ → γ
      ; decode-mapCode = λ γ → ≈-refl (bnd K) (Flow GC (decode K γ))
      })

effectiviseFlow
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K  : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHomFlow GC GC (effectivise K GC)
effectiviseFlow K GC =
  record { preserves-Flow = λ _ → refl⊑ (bnd K) }

-- --------------------------------------------------------------------------
-- Tooling loop: flow-preserving adapters commute with effectivisation
-- up to refinement.

normalize-effective
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (GC  : GuardedClosure (bnd K))
    (GC' : GuardedClosure (bnd K'))
    (h   : KernelHom K K')
  → KernelHomFlow GC GC' h
  → ∀ γ
  → _≼_ (bnd K')
      (map∂ h (decode (effectiveKernel K GC) γ))
      (decode (effectiveKernel K' GC') (mapCode h γ))
normalize-effective {K = K} {K' = K'} GC GC' h HF γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K')
    open R using (begin≼_; _≼⟨_⟩_; _∎≼)
  in
  begin≼
    map∂ h (decode (effectiveKernel K GC) γ)
      ≼⟨ preserves-Flow HF (decode K γ) ⟩
    Flow GC' (map∂ h (decode K γ))
      ≼⟨ GuardedClosure.mono GC' (snd (decode-mapCode h γ)) ⟩
    Flow GC' (decode K' (mapCode h γ)) ∎≼

-- Same theorem, spelled without the effectiveKernel wrapper.
normalize-decode-mapCode
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (GC  : GuardedClosure (bnd K))
    (GC' : GuardedClosure (bnd K'))
    (h   : KernelHom K K')
  → KernelHomFlow GC GC' h
  → ∀ γ
  → _≼_ (bnd K')
      (map∂ h (Flow GC (decode K γ)))
      (Flow GC' (decode K' (mapCode h γ)))
normalize-decode-mapCode {K = K} {K' = K'} GC GC' h HF γ =
  normalize-effective {K = K} {K' = K'} GC GC' h HF γ

-- Short name: “transport commutes with normalisation up to refinement”.
normalize-transport
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (GC  : GuardedClosure (bnd K))
    (GC' : GuardedClosure (bnd K'))
    (h   : KernelHom K K')
  → KernelHomFlow GC GC' h
  → ∀ γ
  → _≼_ (bnd K')
      (map∂ h (Flow GC (decode K γ)))
      (Flow GC' (decode K' (mapCode h γ)))
normalize-transport = normalize-decode-mapCode
