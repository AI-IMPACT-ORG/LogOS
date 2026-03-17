{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Reflection where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Reflection to stable points induced by a guarded closure.
--
-- This is the order-theoretic core of “partial self reference”:
-- out-and-back through stability yields stabilisation (`Flow`), not identity.
--
-- Direction note:
-- `_⊑_ c d` reads as “d is stronger than c”, so the comparison lemmas below
-- witness stabilization/refinement, not equality-on-the-nose. On public theorem
-- surfaces below, `≼` is used as an order-flavoured alias for that same
-- refinement relation.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; refl⊑)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
  module ≼-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Flow using (GuardedClosure; Stable; mkStable; elem; stable)

-- Stable points inherit a preorder from the ambient preorder (by forgetting the witness).
StablePreorder
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (N : Con CP → Con CP)
  → ConPreorder (lsuc (ℓCon ⊔ ℓRel)) ℓRel
StablePreorder {ℓCon} {ℓRel} {CP} N =
  let module R = ≤-Reasoning CP in
  record
    { Con   = Stable {CP = CP} N
    ; _⊑_   = λ x y → ConPreorder._⊑_ CP (elem x) (elem y)
    ; refl  = λ {x} → ConPreorder.refl CP
    ; trans = λ {x} {y} {z} xy yz →
        R._⊑⟨_⟩_ (elem x) xy yz
    }

-- Quotation/evaluation induced by a guarded closure.

quot
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → Con CP → Stable {CP = CP} (GuardedClosure.Flow GC)
quot GC c =
  mkStable
    (GuardedClosure.Flow GC c)
    (GuardedClosure.idemp-lax GC c)

evalm
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → {GC : GuardedClosure CP}
  → Stable {CP = CP} (GuardedClosure.Flow GC) → Con CP
evalm x = elem x

evalm∘quot⊑Flow
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (c : Con CP)
  → _≼_ CP (evalm {GC = GC} (quot GC c)) (GuardedClosure.Flow GC c)
evalm∘quot⊑Flow {CP = CP} GC c = refl⊑ CP

Flow⊑evalm∘quot
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (c : Con CP)
  → _≼_ CP (GuardedClosure.Flow GC c) (evalm {GC = GC} (quot GC c))
Flow⊑evalm∘quot {CP = CP} GC c = refl⊑ CP

evalm∘quot≈Flow
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (c : Con CP)
  → _≈_ CP (evalm {GC = GC} (quot GC c)) (GuardedClosure.Flow GC c)
evalm∘quot≈Flow GC c =
  (evalm∘quot⊑Flow GC c , Flow⊑evalm∘quot GC c)

-- Preorder adjunction (Galois connection): `quot ⊣ evalm`.
--
-- `quot c ⊑ x`  iff  `c ⊑ evalm x`
--
-- Proof uses:
-- - inflationarity: c ⊑ Flow c
-- - stability of x: Flow (elem x) ⊑ elem x
-- - monotonicity of Flow

quot⊣evalm
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (c : Con CP)
  → (x : Stable {CP = CP} (GuardedClosure.Flow GC))
  → _≼_ CP (GuardedClosure.Flow GC c) (elem x)
    ↔ (_≼_ CP c (elem x))
quot⊣evalm {ℓCon} {ℓRel} {CP} GC c x =
  let
    module R = ≼-Reasoning CP
    open R using (begin≼_; _≼⟨_⟩_; _∎≼)
  in
  intro
    (λ fc≤x →
      begin≼
        c ≼⟨ GuardedClosure.infl GC c ⟩
        GuardedClosure.Flow GC c ≼⟨ fc≤x ⟩
        elem x ∎≼)
    (λ c≤x →
      begin≼
        GuardedClosure.Flow GC c ≼⟨ GuardedClosure.mono GC c≤x ⟩
        GuardedClosure.Flow GC (elem x) ≼⟨ stable x ⟩
        elem x ∎≼)
