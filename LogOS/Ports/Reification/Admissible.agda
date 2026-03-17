{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Reification.Admissible where

-- Restricted/staged reification ports (LOGᴳ discipline), packaged as reusable
-- core types.
--
-- A reification step is only assumed up to a guarded closure `Flow`, and is
-- restricted by an explicit admissibility witness (`Reifiable c`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_; _⊑_; sandwich≈)
open import LogOS.LT.Flow using (GuardedClosure; Flow; infl)
open import LogOS.LT.View using (View; μ)

record RestrictedReification
  {ℓX ℓCon ℓRel ℓR : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓCon ℓRel}
  (obs : View X O)
  : Set (lsuc (ℓX ⊔ ℓCon ⊔ ℓRel ⊔ ℓR)) where
  field
    GC : GuardedClosure O

    -- Admissibility ledger: which constraints may be reified as points in `X`.
    Reifiable : Con O → Set ℓR

    -- Reification: map admissible constraints to points in `X`.
    reify : (c : Con O) → Reifiable c → X

    -- Soundness: decoding the reified point matches `Flow`ed constraint.
    decode-reify≈Flow
      : ∀ c r
      → _≈_ O (μ obs (reify c r)) (Flow GC c)

open RestrictedReification public

record TotalReification
  {ℓX ℓCon ℓRel : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓCon ℓRel}
  (obs : View X O)
  : Set (lsuc (ℓX ⊔ ℓCon ⊔ ℓRel)) where
  field
    GC : GuardedClosure O

    reify : Con O → X

    decode-reify≈Flow
      : ∀ c
      → _≈_ O (μ obs (reify c)) (Flow GC c)

open TotalReification public

total→restricted
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → TotalReification obs
  → RestrictedReification {ℓR = ℓR} obs
total→restricted {obs = obs} T =
  record
    { GC = TotalReification.GC T
    ; Reifiable = λ _ → ⊤
    ; reify = λ c _ → TotalReification.reify T c
    ; decode-reify≈Flow = λ c _ → TotalReification.decode-reify≈Flow T c
    }

restricted→total
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → (R : RestrictedReification {ℓR = ℓR} obs)
  → (total : ∀ c → RestrictedReification.Reifiable R c)
  → TotalReification obs
restricted→total {obs = obs} R total =
  record
    { GC = RestrictedReification.GC R
    ; reify = λ c → RestrictedReification.reify R c (total c)
    ; decode-reify≈Flow = λ c → RestrictedReification.decode-reify≈Flow R c (total c)
    }

-- Stability: if `Flow` collapses at `c` (i.e. `Flow c ⊑ c`), then decoding the
-- reified point is observationally equivalent to `c` (no extra `Flow` visible).
decode-reify-stable≈
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → (R : RestrictedReification {ℓR = ℓR} obs)
  → (c : Con O)
  → (r : RestrictedReification.Reifiable R c)
  → _⊑_ O (Flow (RestrictedReification.GC R) c) c
  → _≈_ O (μ obs (RestrictedReification.reify R c r)) c
decode-reify-stable≈ {O = O} {obs = obs} R c r flow≤ =
  sandwich≈ {CP = O}
    (RestrictedReification.decode-reify≈Flow R c r)
    ( infl (RestrictedReification.GC R) c
    , flow≤
    )
