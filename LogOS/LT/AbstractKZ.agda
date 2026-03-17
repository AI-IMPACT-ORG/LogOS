{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.AbstractKZ where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- KZ-style packaging of “Flow + partial reflection”.
--
-- At the boundary level, a guarded closure is exactly the data of a
-- lax-idempotent modality on a preorder: monotone + inflationary + lax-idempotent.
-- (If the preorder is proof-irrelevant, this is the usual one-proof setting; with
-- an added antisymmetry principle you recover the “posetal modality” wording used
-- in some literature.)
--
-- The partial-reflection interface is the induced reflection into stable
-- points (`Stable`), together with the adjunction `quot ⊣ evalm`.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.ConPreorder as Con using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Flow using (GuardedClosure; Stable; Flow)
import LogOS.LT.Reflection
open import LogOS.LT.Theorems.EvaluatorReflection using (reflectEval; reflectEval-infl; reflectEval-NStable; reflectEval-least; NStableEval)

record KZModality {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    GC : GuardedClosure CP

  -- Expose the modality and its stable points.
  N : Con CP → Con CP
  N = Flow GC

  StableN : Set (lsuc (ℓCon ⊔ ℓRel))
  StableN = Stable {CP = CP} N

  -- Partial reflection (quotation/evaluation) into stable points.
  quot : Con CP → StableN
  quot = LogOS.LT.Reflection.quot GC

  evalm : StableN → Con CP
  evalm = LogOS.LT.Reflection.evalm {GC = GC}

  -- Evaluator reflection along the modality (universal property).
  module KZLocal {ℓOCon ℓORel : Level} (O : ConPreorder ℓOCon ℓORel) where
    Reflect : (Con CP → Con O) → Con CP → Con O
    Reflect T = reflectEval {CP = CP} {O = O} GC T

    Reflect-infl
      : (T : Con CP → Con O)
      → Con.MonoMap CP O T
      → _⊑_ (LogOS.LT.Theorems.EvaluatorReflection.EvalPreorder CP O) T (Reflect T)
    Reflect-infl T monoT = reflectEval-infl {CP = CP} {O = O} GC T monoT

    Reflect-NStable : (T : Con CP → Con O) → Con.MonoMap CP O T → NStableEval {CP = CP} {O = O} GC (Reflect T)
    Reflect-NStable T monoT = reflectEval-NStable {CP = CP} {O = O} GC T monoT

    Reflect-least
      : (T S : Con CP → Con O)
      → Con.MonoMap CP O T
      → _⊑_ (LogOS.LT.Theorems.EvaluatorReflection.EvalPreorder CP O) T S
      → NStableEval {CP = CP} {O = O} GC S
      → _⊑_ (LogOS.LT.Theorems.EvaluatorReflection.EvalPreorder CP O) (Reflect T) S
    Reflect-least T S monoT T≤S stableS =
      reflectEval-least {CP = CP} {O = O} GC T S monoT T≤S stableS

  quot⊣evalm
    : ∀ (c : Con CP) (x : StableN)
    → _⊑_ CP (N c) (Stable.elem x) ↔ _⊑_ CP c (Stable.elem x)
  quot⊣evalm = LogOS.LT.Reflection.quot⊣evalm GC

-- Intentionally *not* opened publicly:
-- the record provides convenience projections (e.g. `KZModality.N`) but
-- re-exporting them unqualified clashes with core names like `quot`/`evalm`
-- from `LogOS.LT.Reflection`.
