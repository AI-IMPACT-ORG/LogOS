{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.PacketCorollaries where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Corollaries (core consequences) for closure-based (effective) semantics.
--
-- These are generic consequences of:
-- - a chosen boundary preorder,
-- - a chosen guarded closure `Flow`,
-- - and the induced effective observation `effObs = Flow ∘ decode`.
--
-- Non-abelian “packet” phenomena are boundary-level here: packets are exactly
-- equivalence in the effective observation, and stable evaluators cannot see
-- packet mates.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap; ≈-refl)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; CodePreorder)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Theorems.EvaluatorReflection using
  ( EvalPreorder
  ; NStableEval
  ; reflectEval
  ; reflectEval-maximally-safe
  )

open import LogOS.LT.Theorems.Effectivisation using (effectiveKernel)
open import LogOS.LT.Theorems.EffectivePackets using
  ( effObs
  ; Packet
  )
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- --------------------------------------------------------------------------
-- Packets are code-equivalence in the unrolled (effective) kernel.

Packet-refl
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    (GC : GuardedClosure (bnd K))
  → ∀ γ → Packet {K = K} GC γ γ
Packet-refl {K = K} GC γ = ≈-refl (bnd K) (effObs {K = K} GC γ)

Packet-sym
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {GC : GuardedClosure (bnd K)}
    {γ δ : Code K}
  → Packet {K = K} GC γ δ → Packet {K = K} GC δ γ
Packet-sym (γ≤δ , δ≤γ) = (δ≤γ , γ≤δ)

Packet-trans
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {GC : GuardedClosure (bnd K)}
    {γ δ ε : Code K}
  → Packet {K = K} GC γ δ → Packet {K = K} GC δ ε → Packet {K = K} GC γ ε
Packet-trans {K = K} {GC = GC} {γ = γ} {δ = δ} {ε = ε} (γ≤δ , δ≤γ) (δ≤ε , ε≤δ) =
  let
    module R = ≤-Reasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  ( (begin⊑
       effObs {K = K} GC γ ⊑⟨ γ≤δ ⟩
       effObs {K = K} GC δ ⊑⟨ δ≤ε ⟩
       effObs {K = K} GC ε ∎⊑)
  , (begin⊑
       effObs {K = K} GC ε ⊑⟨ ε≤δ ⟩
       effObs {K = K} GC δ ⊑⟨ δ≤γ ⟩
       effObs {K = K} GC γ ∎⊑)
  )

Packet↔Code≈-effectiveKernel
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    (GC : GuardedClosure (bnd K))
  → ∀ γ δ
  → Packet {K = K} GC γ δ
    ↔
    _≈_ (CodePreorder (effectiveKernel K GC)) γ δ
Packet↔Code≈-effectiveKernel _ _ _ =
  intro
    (λ p → p)
    (λ p → p)

-- --------------------------------------------------------------------------
-- “Packets are the only invariants”: stable evaluators cannot distinguish them.

-- Any monotone boundary evaluator becomes packet-invariant once you reflect it
-- through `Flow` (i.e. once you only observe effective semantics).
packet-invariant-effective
  : ∀ {ℓ ℓRel ℓCode ℓOCon ℓORel : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    (GC : GuardedClosure (bnd K))
    {O : ConPreorder ℓOCon ℓORel}
    (T : Con (bnd K) → Con O)
  → MonoMap (bnd K) O T
  → ∀ {γ δ}
  → Packet {K = K} GC γ δ
  → _≈_ O (T (effObs {K = K} GC γ)) (T (effObs {K = K} GC δ))
packet-invariant-effective {K = K} GC T monoT (γ≤δ , δ≤γ) =
  (monoT γ≤δ , monoT δ≤γ)

-- Stronger: if an evaluator is already stable w.r.t. `Flow`, then it cannot
-- distinguish packet mates even *before* reflecting.
packet-indistinguishable
  : ∀ {ℓ ℓRel ℓCode ℓOCon ℓORel : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    (GC : GuardedClosure (bnd K))
    {O : ConPreorder ℓOCon ℓORel}
    (T : Con (bnd K) → Con O)
  → MonoMap (bnd K) O T
  → NStableEval {CP = bnd K} {O = O} GC T
  → ∀ {γ δ}
  → Packet {K = K} GC γ δ
  → _≈_ O (T (decode K γ)) (T (decode K δ))
packet-indistinguishable {K = K} GC {O = O} T monoT (TFlow≤T , T≤TFlow) {γ = γ} {δ = δ} (γ≤δ , δ≤γ) =
  (γ≤δ' , δ≤γ')
  where
    module R = ≤-Reasoning O
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)

    γ≤δ'
      : _⊑_ O (T (decode K γ)) (T (decode K δ))
    γ≤δ' =
      begin⊑
        T (decode K γ) ⊑⟨ T≤TFlow (decode K γ) ⟩
        T (effObs {K = K} GC γ) ⊑⟨ monoT γ≤δ ⟩
        T (effObs {K = K} GC δ) ⊑⟨ TFlow≤T (decode K δ) ⟩
        T (decode K δ) ∎⊑

    δ≤γ'
      : _⊑_ O (T (decode K δ)) (T (decode K γ))
    δ≤γ' =
      begin⊑
        T (decode K δ) ⊑⟨ T≤TFlow (decode K δ) ⟩
        T (effObs {K = K} GC δ) ⊑⟨ monoT δ≤γ ⟩
        T (effObs {K = K} GC γ) ⊑⟨ TFlow≤T (decode K γ) ⟩
        T (decode K γ) ∎⊑

-- A handy rewriting lemma: “reflecting on the boundary” is the same as
-- “evaluating the effective observation”.
reflectEval≈T∘effObs
  : ∀ {ℓ ℓRel ℓCode ℓOCon ℓORel : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    (GC : GuardedClosure (bnd K))
    {O : ConPreorder ℓOCon ℓORel}
    (T : Con (bnd K) → Con O)
  → ∀ γ
  → _≈_ O
      (reflectEval {CP = bnd K} {O = O} GC T (decode K γ))
      (T (effObs {K = K} GC γ))
reflectEval≈T∘effObs {K = K} GC {O = O} T γ =
  ≈-refl O (T (effObs {K = K} GC γ))

-- “Maximally safe packet invariant”: reflecting an evaluator through `Flow`
-- is the least `Flow`-stable evaluator above it.
maximally-safe-packetInvariant
  : ∀ {ℓYCon ℓYRel ℓOCon ℓORel : Level}
    {CP : ConPreorder ℓYCon ℓYRel}
    {O  : ConPreorder ℓOCon ℓORel}
    (GC : GuardedClosure CP)
    (T  : Con CP → Con O)
    (monoT : MonoMap CP O T)
  → NStableEval {CP = CP} {O = O} GC (reflectEval {CP = CP} {O = O} GC T)
    ×
    (∀ S
      → MonoMap CP O S
      → _⊑_ (EvalPreorder CP O) T S
      → NStableEval {CP = CP} {O = O} GC S
      → _⊑_ (EvalPreorder CP O) (reflectEval {CP = CP} {O = O} GC T) S)
maximally-safe-packetInvariant {CP = CP} {O = O} GC T monoT =
  reflectEval-maximally-safe {CP = CP} {O = O} GC T monoT
