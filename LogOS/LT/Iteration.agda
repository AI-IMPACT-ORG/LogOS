{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Iteration where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Iteration/trace utilities (design-target spec).
--
-- See spec v5.8 “Literal reading: representations, translations, and computation”,
-- especially “Computation as encode--iterate--decode--normalise” and the lemma
-- “boundary reduction of iteration”.
--
-- No new primitives: we spell out how decode coherence reduces iterated
-- computation to boundary dynamics.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoOn; refl⊑; monoMap-≈)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; map∂-mono; mapCode; decode-mapCode)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Sup.FinSup using (FinSup)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO)
open import LogOS.LT.Stage.SuccessorChain using (Stageω; zero; suc; iterω)
import LogOS.LT.Sup.SupOmega
-- Function iteration (apply `f` n times).
iter : ∀ {ℓ} {A : Set ℓ} → (A → A) → Stageω → A → A
iter = iterω

-- Code-level trace under a step transformer.
traceCode
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (f : KernelHom K K)
  → (n : Stageω)
  → Code K → Code K
traceCode f n γ = iter (mapCode f) n γ

-- Boundary observation trace.
traceBnd
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (f : KernelHom K K)
  → (n : Stageω)
  → Code K → Con (bnd K)
traceBnd {K = K} f n γ = decode K (traceCode f n γ)

-- Boundary reduction of iteration (decode commutes with iterated code steps).
private
  MonoOnᵉ
    : ∀ {ℓCon ℓRel} (CP : ConPreorder ℓCon ℓRel)
    → (Con CP → Con CP)
    → Set (ℓCon ⊔ ℓRel)
  MonoOnᵉ CP f = (x y : Con CP) → _⊑_ CP x y → _⊑_ CP (f x) (f y)

  mono→ᵉ
    : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel} {f : Con CP → Con CP}
    → MonoOn CP f
    → MonoOnᵉ CP f
  mono→ᵉ mono x y xy = mono {x = x} {y = y} xy

  iter-monoᵉ
    : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
      {f : Con CP → Con CP}
    → (n : Stageω)
    → MonoOnᵉ CP f
    → MonoOnᵉ CP (iter f n)
  iter-monoᵉ zero    mono x y xy = xy
  iter-monoᵉ {CP = CP} {f = f} (suc n) mono x y xy =
    iter-monoᵉ {CP = CP} {f = f} n mono (f x) (f y) (mono x y xy)

  iter-mono
    : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
      {f : Con CP → Con CP}
    → (n : Stageω)
    → MonoOn CP f
    → MonoOnᵉ CP (iter f n)
  iter-mono {CP = CP} {f = f} n mono =
    iter-monoᵉ {CP = CP} {f = f} n (mono→ᵉ {CP = CP} {f = f} mono)

decode-iter-mapCode⊑
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (f : KernelHom K K)
  → (n : Stageω)
  → (γ : Code K)
  → _⊑_ (bnd K)
      (decode K (iter (mapCode f) n γ))
      (iter (map∂ f) n (decode K γ))
decode-iter-mapCode⊑ {K = K} f zero    γ = refl⊑ (bnd K)
decode-iter-mapCode⊑ {K = K} f (suc n) γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    decode K (iter (mapCode f) (suc n) γ)
      ⊑⟨ decode-iter-mapCode⊑ {K = K} f n (mapCode f γ) ⟩
    iter (map∂ f) n (decode K (mapCode f γ))
      ⊑⟨ iter-mono {CP = bnd K} {f = map∂ f} n (map∂-mono f)
           (decode K (mapCode f γ))
           (map∂ f (decode K γ))
           (fst (decode-mapCode f γ)) ⟩
    iter (map∂ f) n (map∂ f (decode K γ)) ∎⊑

decode-iter-mapCode⊒
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (f : KernelHom K K)
  → (n : Stageω)
  → (γ : Code K)
  → _⊑_ (bnd K)
      (iter (map∂ f) n (decode K γ))
      (decode K (iter (mapCode f) n γ))
decode-iter-mapCode⊒ {K = K} f zero    γ = refl⊑ (bnd K)
decode-iter-mapCode⊒ {K = K} f (suc n) γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    iter (map∂ f) n (map∂ f (decode K γ))
      ⊑⟨ iter-mono {CP = bnd K} {f = map∂ f} n (map∂-mono f)
           (map∂ f (decode K γ))
           (decode K (mapCode f γ))
           (snd (decode-mapCode f γ)) ⟩
    iter (map∂ f) n (decode K (mapCode f γ))
      ⊑⟨ decode-iter-mapCode⊒ {K = K} f n (mapCode f γ) ⟩
    decode K (iter (mapCode f) (suc n) γ) ∎⊑

decode-iter-mapCode
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (f : KernelHom K K)
  → (n : Stageω)
  → (γ : Code K)
  → _≈_ (bnd K)
      (decode K (iter (mapCode f) n γ))
      (iter (map∂ f) n (decode K γ))
decode-iter-mapCode f n γ =
  (decode-iter-mapCode⊑ f n γ , decode-iter-mapCode⊒ f n γ)

traceBnd-reduce
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (f : KernelHom K K)
  → (n : Stageω)
  → (γ : Code K)
  → _≈_ (bnd K) (traceBnd f n γ) (iter (map∂ f) n (decode K γ))
traceBnd-reduce f n γ = decode-iter-mapCode f n γ

mono-preserves≈
  : ∀ {ℓCon ℓRel}
    (CP : ConPreorder ℓCon ℓRel)
    (f : Con CP → Con CP)
  → MonoOn CP f
  → ∀ {x y}
  → _≈_ CP x y
  → _≈_ CP (f x) (f y)
mono-preserves≈ CP f mono {x} {y} eq =
  monoMap-≈ {CP₁ = CP} {CP₂ = CP} {f = f} mono x y eq

-- Optional: normalised trace given a guarded-closure doctrine on the boundary.
normTrace
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → (f : KernelHom K K)
  → (n : Stageω)
  → Code K → Con (bnd K)
normTrace {K = K} GC f n γ = GuardedClosure.Flow GC (traceBnd {K = K} f n γ)

normTrace-reduce
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → (f : KernelHom K K)
  → (n : Stageω)
  → (γ : Code K)
  → _≈_ (bnd K)
      (normTrace {K = K} GC f n γ)
      (GuardedClosure.Flow GC (iter (map∂ f) n (decode K γ)))
normTrace-reduce {K = K} GC f n γ =
  mono-preserves≈ (bnd K) (GuardedClosure.Flow GC) (GuardedClosure.mono GC)
    (traceBnd-reduce {K = K} f n γ)

-- Optional: full “run” result via ω-supremum of the normalised trace.
--
-- In v1.1 this is derived from:
-- - finite joins (`FinSup`) and
-- - σ-directed ω-suprema (`SigmaDCPO`),
-- by taking the σ-supremum of the directed chain of finite prefix-joins.
run
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → (FS : FinSup (bnd K))
  → (SD : SigmaDCPO (bnd K))
  → (f : KernelHom K K)
  → Code K → Con (bnd K)
run {K = K} GC FS SD f γ = Supω.supω (λ n → normTrace {K = K} GC f n γ)
  where
    module Supω = LogOS.LT.Sup.SupOmega.SupOmegaSection FS SD
