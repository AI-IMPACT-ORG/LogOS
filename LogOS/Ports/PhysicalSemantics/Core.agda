{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PhysicalSemantics.Core where

-- Shared, distributed semantics ledger.
--
-- This is a small record that packages the concrete v1.1 notion of
-- shared distributed observation plus a local closure doctrine:
--
-- - one locality index `I`,
-- - an index-dependent local observation family `O : I → ConPreorder … …`,
-- - an index-dependent local causal/effective doctrine
--   `GC₀ i : GuardedClosure (O i)`,
-- lifted pointwise to the shared dependent boundary
--   `Bnd = LocalBoundary I O`.
--
-- It intentionally does *not* add any kernel axioms: it is a convenient
-- semantics ledger that downstream packs can reuse.
-- A physics-style reading is optional and belongs to the pack that chooses the
-- locality index, local observables, and local doctrine.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.Ports.Locality.Core using (LocalBoundary)
open import LogOS.Ports.Locality.Lifts using (pointwiseClosure)
open import LogOS.LT.Effectivity using (Effectivity)

-- Dependent variant: the local observation preorder (and hence the doctrine)
-- may vary with the locality index.
record DependentLocalSemantics {ℓI ℓOCon ℓORel : Level}
  : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    I   : Set ℓI
    O   : I → ConPreorder ℓOCon ℓORel
    GC₀ : (i : I) → GuardedClosure (O i)

  Bnd : ConPreorder (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel)
  Bnd = LocalBoundary I O

  GC : GuardedClosure Bnd
  GC = pointwiseClosure {I = I} {O = O} GC₀

  -- Effectivity packaging (lightweight vocabulary layer).
  Eff₀ : (i : I) → Effectivity (O i)
  Eff₀ i = record { GC = GC₀ i }

  Eff : Effectivity Bnd
  Eff = record { GC = GC }

-- Two-stage (iterated) modality ledger: a dependent shared-semantics ledger `PS`
-- together with an additional closure/modality on the same shared boundary.
--
-- This is the minimal way to model “local doctrine + additional modality”
-- without changing the locality injection discipline: translations can remain
-- pointwise, and extra (non-pointwise) structure lives in an explicit closure.
record TwoStageDependentLocalSemantics {ℓI ℓOCon ℓORel : Level}
  : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    PS  : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}
    GC₁ : GuardedClosure (DependentLocalSemantics.Bnd PS)

  I : Set ℓI
  I = DependentLocalSemantics.I PS

  O : I → ConPreorder ℓOCon ℓORel
  O = DependentLocalSemantics.O PS

  GC₀ : (i : I) → GuardedClosure (O i)
  GC₀ = DependentLocalSemantics.GC₀ PS

  Bnd : ConPreorder (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel)
  Bnd = DependentLocalSemantics.Bnd PS

  GC : GuardedClosure Bnd
  GC = DependentLocalSemantics.GC PS

  -- Effectivity packaging at each stage.
  Eff₀ : (i : I) → Effectivity (O i)
  Eff₀ i = record { GC = GC₀ i }

  Eff : Effectivity Bnd
  Eff = record { GC = GC }

  Eff₁ : Effectivity Bnd
  Eff₁ = record { GC = GC₁ }

  -- Two-stage normalisation on the boundary carrier.
  --
  -- Note: this is composition of the chosen modalities on `Bnd`; no claim
  -- is made that it is itself a guarded closure.
  normalize² : Con Bnd → Con Bnd
  normalize² c = Flow GC₁ (Flow GC c)
