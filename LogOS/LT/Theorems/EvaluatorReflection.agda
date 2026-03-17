{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.EvaluatorReflection where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Reflection of evaluators along a guarded closure (design-target spec).
--
-- See spec v5.8 “Reflection of evaluators along closure”.
--
-- Let (Y,⊑) be a preorder and N : Y → Y a guarded closure:
--   - monotone, inflationary, and lax-idempotent.
--
-- For any monotone evaluator T : Y → O into some target preorder O, define:
--   T^N ≡ T ∘ N.
--
-- Then:
--  (1) T ≼ T^N
--  (2) T^N ∘ N ≈ T^N
--  (3) For any N-stable S with T ≼ S, we have T^N ≼ S.
--
-- This is a precise formulation of the “maximal safe reflection” principle:
-- out-and-back stabilises via N (not identity), and is universal among N-stable evaluators.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.LT.ConPreorder as Con using (ConPreorder; Con; _⊑_; MonoMap)
open import LogOS.LT.FunPreorder using (FunPreorder)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
  module ≼-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- Pointwise refinement on evaluators.
EvalPreorder
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
  → (CP : ConPreorder ℓYCon ℓYRel)
  → (O  : ConPreorder ℓOCon ℓORel)
  → ConPreorder (ℓYCon ⊔ ℓOCon) (ℓYCon ⊔ ℓORel)
EvalPreorder CP O = FunPreorder (Con CP) O

-- Precomposition by the guarded closure.
reflectEval
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
  → GuardedClosure CP
  → (Con CP → Con O)
  → Con CP → Con O
reflectEval GC T c = T (Flow GC c)

-- If T is monotone, so is T ∘ N.
reflectEval-mono
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
    (GC : GuardedClosure CP)
    (T  : Con CP → Con O)
  → MonoMap CP O T
  → MonoMap CP O (reflectEval {CP = CP} {O = O} GC T)
reflectEval-mono GC T monoT le = monoT (GuardedClosure.mono GC le)

-- (1) Inflation: T ≼ T ∘ N.
reflectEval-infl
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
    (GC : GuardedClosure CP)
    (T  : Con CP → Con O)
  → MonoMap CP O T
  → _≼_ (EvalPreorder CP O) T (reflectEval {CP = CP} {O = O} GC T)
reflectEval-infl GC T monoT c = monoT (GuardedClosure.infl GC c)

-- N-stability of an evaluator (up to mutual refinement).
--
-- Name note: `Stable` is reserved for stable boundary *points* (`Flow.Stable`).
-- Evaluator stability is “N-stability”, to avoid overloading.
NStableEval
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
  → GuardedClosure CP
  → (Con CP → Con O)
  → Set (ℓYCon ⊔ ℓORel)
NStableEval {CP = CP} {O = O} GC T =
  (_≼_ (EvalPreorder CP O)
    (reflectEval {CP = CP} {O = O} GC T)
    T)
  ×
  (_≼_ (EvalPreorder CP O)
    T
    (reflectEval {CP = CP} {O = O} GC T))

-- (2) N-stability: (T ∘ N) ∘ N ≈ (T ∘ N).
reflectEval-NStable
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
    (GC : GuardedClosure CP)
    (T  : Con CP → Con O)
  → MonoMap CP O T
  → NStableEval {CP = CP} {O = O} GC (reflectEval {CP = CP} {O = O} GC T)
reflectEval-NStable {CP = CP} {O = O} GC T monoT =
  ( forward , backward )
  where
    forward
      : _≼_ (EvalPreorder CP O)
          (reflectEval {CP = CP} {O = O} GC (reflectEval {CP = CP} {O = O} GC T))
          (reflectEval {CP = CP} {O = O} GC T)
    forward c = monoT (GuardedClosure.idemp-lax GC c)

    backward
      : _≼_ (EvalPreorder CP O)
          (reflectEval {CP = CP} {O = O} GC T)
          (reflectEval {CP = CP} {O = O} GC (reflectEval {CP = CP} {O = O} GC T))
    backward c = monoT (GuardedClosure.infl GC (Flow GC c))

-- (3) Universal property: T ∘ N is the least N-stable evaluator above T.
reflectEval-least
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
    (GC : GuardedClosure CP)
    (T S : Con CP → Con O)
  → MonoMap CP O T
  → _≼_ (EvalPreorder CP O) T S
  → NStableEval {CP = CP} {O = O} GC S
  → _≼_ (EvalPreorder CP O) (reflectEval {CP = CP} {O = O} GC T) S
reflectEval-least {CP = CP} {O = O} GC T S monoT T≤S (SN≤S , S≤SN) c =
  let
    module R = ≼-Reasoning O
    open R using (begin≼_; _≼⟨_⟩_; _∎≼)
  in
  begin≼
    T (Flow GC c) ≼⟨ T≤S (Flow GC c) ⟩
    S (Flow GC c) ≼⟨ SN≤S c ⟩
    S c ∎≼

-- Human-readable “maximal safe reflection” naming.
-- The reflected evaluator is always stable and is the least such
-- reflection above the original evaluator.
reflectEval-maximally-safe
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel}
    {CP : ConPreorder ℓYCon ℓYRel} {O : ConPreorder ℓOCon ℓORel}
    (GC : GuardedClosure CP)
    (T  : Con CP → Con O)
    (monoT : MonoMap CP O T)
  → NStableEval {CP = CP} {O = O} GC (reflectEval {CP = CP} {O = O} GC T)
  ×
  (∀ S
    → MonoMap CP O S
    → _≼_ (EvalPreorder CP O) T S
    → NStableEval {CP = CP} {O = O} GC S
    → _≼_ (EvalPreorder CP O) (reflectEval {CP = CP} {O = O} GC T) S)
reflectEval-maximally-safe {CP = CP} {O = O} GC T monoT =
  ( reflectEval-NStable {CP = CP} {O = O} GC T monoT
  , λ S monoS T≤S stableS →
      reflectEval-least {CP = CP} {O = O} GC T S monoT T≤S stableS
  )
