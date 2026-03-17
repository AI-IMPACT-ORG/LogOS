{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Reflection.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-facing reflection laws.
--
-- The core reflection construction remains in `LogOS.LT.Reflection`; this
-- module makes the law surface explicit and coherence-indexed.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.Coherence using (CohMode; CohRel; CohLevel; approx; under)
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Flow using (GuardedClosure; Stable)
open import LogOS.LT.Reflection using
  ( quot
  ; evalm
  ; evalm∘quot⊑Flow
  ; evalm∘quot≈Flow
  ; quot⊣evalm
  )

evalm∘quot-law
  : ∀ {m : CohMode} {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (c : Con CP)
  → CohRel m CP (evalm {GC = GC} (quot GC c)) (GuardedClosure.Flow GC c)
evalm∘quot-law {m = approx} GC c = evalm∘quot≈Flow GC c
evalm∘quot-law {m = under} GC c = evalm∘quot⊑Flow GC c

record ReflectionLawLike
  (m : CohMode)
  {ℓCon ℓRel : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (GC : GuardedClosure CP)
  : Set (lsuc (ℓCon ⊔ CohLevel m ℓCon ℓRel)) where
  field
    evalm∘quot-law-at : ∀ c → CohRel m CP (evalm {GC = GC} (quot GC c)) (GuardedClosure.Flow GC c)

open ReflectionLawLike public

reflectionLawLike
  : ∀ {m : CohMode} {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → ReflectionLawLike m GC
reflectionLawLike {m = m} GC =
  record
    { evalm∘quot-law-at = evalm∘quot-law {m = m} GC
    }

quot⊣evalm-law
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (c : Con CP)
  → (x : Stable {CP = CP} (GuardedClosure.Flow GC))
  → _≼_ CP (GuardedClosure.Flow GC c) (LogOS.LT.Flow.elem x)
    ↔ (_≼_ CP c (LogOS.LT.Flow.elem x))
quot⊣evalm-law = quot⊣evalm
