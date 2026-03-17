{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutschNoCloning where

-- Side-car to `LogOS.Ports.AbstractDeutsch2Cat`.
-- a refinement-first “no-cloning” thread that stays within the existing spine.
--
-- What is formalised here (3 layers):
--
-- 1. (Reversible fragment) The diagonal map Δ : O → O×O cannot have a
--    refinement-inverse unless O is indiscrete (all points mutually refine).
--    This is the categorical core of no-cloning: reversible physics is not
--    cartesian.
--
-- 2. (Normalisation gate) Any kernel can be completed into stable points
--    via `stableCompletion`, and only after this `Flow`-normalisation do we
--    obtain a canonical “copy the code” cloner. This is the quine-like pattern
--    with meaning injected through the choice of doctrine `GC`.
--
-- 3. (Quantitative side) With a finite-join `QAdapter`, the “two outputs”
--    grade combiner is taken to be `⊔s` (join): cloning is grade-neutral via
--    join-idempotence, preserving the existing grade semantics.

open import LogOS.Prelude using
  ( Level
  ; _⊔_
  ; refl
  ; fst
  ; snd
  ; _,_
  ; _×_
  )
open import LogOS.LT.ConPreorder using
    ( ConPreorder
    ; Con
    ; _⊑_
    ; _≈_
    ; refl⊑
    ; MonoMap
    ; _×CP_
    ; diag
    ; diag-mono
    )
open import LogOS.LT.Coherence using (approx)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; Kernel×)
open import LogOS.LT.Hom.Core using
    ( KernelHom
    ; mkKernelHomParts
    ; _∘_
    ; map∂
    ; mapCode
    ; map∂-mono
    ; decode-mapCode
    )
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.LOG.QuotePort2Cat using (quoteKernel)
open import LogOS.LT.Theorems.StableCompletion using (stableCompletion; stableCompletion-law)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary)

-- --------------------------------------------------------------------------
-- 1) The preorder-level obstruction: diagonal is not reversible.

Indiscrete
  : ∀ {ℓCon ℓRel : Level}
  → ConPreorder ℓCon ℓRel
  → Set (ℓCon ⊔ ℓRel)
Indiscrete O = ∀ x y → _≈_ O x y

-- “No-cloning” lemma (preorder form):
-- if Δ has a section up to mutual refinement, the preorder is indiscrete.
diag-section→indiscrete
  : ∀ {ℓCon ℓRel : Level} {O : ConPreorder ℓCon ℓRel}
  → (merge : Con (O ×CP O) → Con O)
  → MonoMap (O ×CP O) O merge
  → (∀ p → _≈_ (O ×CP O) (diag {O = O} (merge p)) p)
  → Indiscrete O
diag-section→indiscrete {O = O} merge _ sec x y =
  ( x⊑y , y⊑x )
    where
      CP× = O ×CP O
      module R = LogOS.Prelude.RefinementKit.Reasoning O
      open R
      m : Con O
      m = merge (x , y)

      secxy : _≈_ CP× (diag {O = O} m) (x , y)
      secxy = sec (x , y)

      forward : _⊑_ CP× (diag {O = O} m) (x , y)
      forward = fst secxy

      backward : _⊑_ CP× (x , y) (diag {O = O} m)
      backward = snd secxy

      x⊑y : _⊑_ O x y
      x⊑y =
        begin⊑
          x ⊑⟨ fst backward ⟩
          m ⊑⟨ snd forward ⟩
          y ∎⊑

      y⊑x : _⊑_ O y x
      y⊑x =
        begin⊑
          y ⊑⟨ snd backward ⟩
          m ⊑⟨ fst forward ⟩
          x ∎⊑

-- --------------------------------------------------------------------------
-- 2) Kernel-level cloning, and the stable/quote normalisation gate.

cloneKernel
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
  → KernelHom K (Kernel× K K)
cloneKernel K =
  mkKernelHomParts
    (record
      { map∂ = diag {O = bnd K}
      ; map∂-mono = diag-mono {O = bnd K}
      })
    (record
      { mapCode = λ γ → (γ , γ)
      ; decode-mapCode = λ _ →
          ( refl⊑ (bnd K ×CP bnd K)
          , refl⊑ (bnd K ×CP bnd K)
          )
      })

-- Stable-point cloning (copy the stable code).
cloneStable
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    (GC : GuardedClosure (bnd K))
  → KernelHom (quoteKernel GC) (Kernel× (quoteKernel GC) (quoteKernel GC))
cloneStable {K = K} GC =
  cloneKernel (quoteKernel GC)

-- Canonical “clone after normalisation” for any kernel.
--
-- This is the quine-shaped factorisation:
--   K  --stableCompletion/Flow-->  Stable(K)  --copy code-->  Stable(K)×Stable(K).
stableClone
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → KernelHom K (Kernel× (quoteKernel GC) (quoteKernel GC))
stableClone K GC =
  cloneStable {K = K} GC ∘ stableCompletion K GC

-- Spelled-out semantics: the cloned meaning is *normalised* meaning.
stableClone-law
  : ∀ {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (GC : GuardedClosure (bnd K))
  → ∀ γ
  → _≈_ (bnd K ×CP bnd K)
      (decode (Kernel× (quoteKernel GC) (quoteKernel GC))
        (mapCode (stableClone K GC) γ))
      ( Flow GC (decode K γ)
      , Flow GC (decode K γ)
      )
stableClone-law K GC γ =
  ( forward , backward )
  where
    law
      : _≈_ (bnd K)
          (decode (quoteKernel GC) (mapCode (stableCompletion K GC) γ))
          (Flow GC (decode K γ))
    law = stableCompletion-law {m = approx} K GC γ

    forward : _⊑_ (bnd K ×CP bnd K)
      (decode (Kernel× (quoteKernel GC) (quoteKernel GC))
        (mapCode (stableClone K GC) γ))
      ( Flow GC (decode K γ)
      , Flow GC (decode K γ)
      )
    forward = (fst law , fst law)

    backward : _⊑_ (bnd K ×CP bnd K)
      ( Flow GC (decode K γ)
      , Flow GC (decode K γ)
      )
      (decode (Kernel× (quoteKernel GC) (quoteKernel GC))
        (mapCode (stableClone K GC) γ))
    backward = (snd law , snd law)

-- --------------------------------------------------------------------------
-- 3) Quantitative side-car: join makes cloning grade-neutral.

module DeutschNoCloningLocal {ℓ : Level} (Q : QAdapter ℓ) where
  open QAdapter Q
  infix 4 _≈s_
  _≈s_ : Scale → Scale → Set ℓ
  _≈s_ = _≈_ (ScaleBoundary Q)

  -- Join idempotence holds propositionally from the semilattice axioms.
  ⊔s-idem : ∀ a → (a ⊔s a) ≈s a
  ⊔s-idem a =
    ( ⊔s-least ≤s-refl ≤s-refl
    , ⊔s-ub₁ a a
    )
