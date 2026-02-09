{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.CategoryTheoryCoherence where

-- Regression: the conservative “hyperdoctrine-shaped” coherence lemmas are
-- usable in a concrete kernel.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Adjunction using (LaxAdjunction; LaxMonoidalAdjunction)
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Hom using (idKernelHom)

import LogOS.UniversalIR.Examples.KernelSaturationLaxTasksNontrivial as Ex

import LogOS.Theorems.CategoryTheory.AdjunctionMonads as AdjunctionMonads
import LogOS.Theorems.CategoryTheory.BeckChevalley as BeckChevalley

-- Frobenius specialized to a kernel.
module Frob = AdjunctionMonads.ForKernelFrobenius Ex.Kℕ

frobenius-ext≤-Kℕ' : _
frobenius-ext≤-Kℕ' = Frob.frobenius-ext≤

-- Target adjunction monotonicity (trivial here because ext/bnd are identity).

ext-mono-Kℕ
  : ∀ {c c'}
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB Ex.Kℕ)) c c'
  → ConPreorder._⊑_ (BulkBoundary.bulk (Kernel.BB Ex.Kℕ))
      (LaxAdjunction.ext (LaxMonoidalAdjunction.core (Kernel.Holo Ex.Kℕ)) c)
      (LaxAdjunction.ext (LaxMonoidalAdjunction.core (Kernel.Holo Ex.Kℕ)) c')
ext-mono-Kℕ le = le

bnd-mono-Kℕ
  : ∀ {d d'}
  → ConPreorder._⊑_ (BulkBoundary.bulk (Kernel.BB Ex.Kℕ)) d d'
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB Ex.Kℕ))
      (LaxAdjunction.bnd (LaxMonoidalAdjunction.core (Kernel.Holo Ex.Kℕ)) d)
      (LaxAdjunction.bnd (LaxMonoidalAdjunction.core (Kernel.Holo Ex.Kℕ)) d')
bnd-mono-Kℕ le = le

-- Beck–Chevalley squares from the identity kernel hom, and the induced closure preservation.

module BC =
  BeckChevalley.FromKernelHom
    {K₁ = Ex.Kℕ} {K₂ = Ex.Kℕ}
    (idKernelHom Ex.Kℕ)

map∂-T-lax-id-Kℕ' : _
map∂-T-lax-id-Kℕ' = BC.map∂-T-lax bnd-mono-Kℕ

mapb-S-lax-id-Kℕ' : _
mapb-S-lax-id-Kℕ' = BC.mapb-S-lax ext-mono-Kℕ
