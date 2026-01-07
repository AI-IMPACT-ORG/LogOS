{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.BoundaryFixFromScott where

open import LogOS.Prelude
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Assumptions.Core

-- A per-function Scott-style fixed point witness on a given constraint poset.
record ScottFix {ℓ} (CP : ConPoset ℓ)
                 (f : ConPoset.Con CP → ConPoset.Con CP)
                 : Set (lsuc ℓ) where
  open ConPoset CP
  field
    fixed : Σ (Con) (λ c → c ≡ f c)

-- Construct a `BoundaryFix` instance for a kernel from any per-function fixed-point
-- provider on the boundary poset (e.g. obtained from Scott/Knaster–Tarski reasoning
-- in concrete models). This keeps `BoundaryFix` explicit and avoids global postulates.

BoundaryFix-from-Scott
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    → (∀ (f : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)) → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
        → MonoOn (BulkBoundary.bnd (Kernel.BB K)) f
        → ScottFix (BulkBoundary.bnd (Kernel.BB K)) f)
    → BoundaryFix K
BoundaryFix-from-Scott K SF = record
  { fixH = λ f mono →
      let CP = BulkBoundary.bnd (Kernel.BB K)
          pair = ScottFix.fixed (SF f mono)
          c    = proj₁ pair
          eq   = proj₂ pair
          c≤fc : ConPoset._⊑_ CP c (f c)
          c≤fc = subst (λ x → ConPoset._⊑_ CP c x) eq (ConPoset.refl CP {c = c})
          fc≤c : ConPoset._⊑_ CP (f c) c
          fc≤c = subst (λ x → ConPoset._⊑_ CP (f c) x) (sym eq) (ConPoset.refl CP {c = f c})
      in c , (c≤fc , fc≤c)
  }

-- Note: The constructor above is schematic — in practical models, `Scott f` should carry
-- a fixed-point witness; the `BoundaryFix` interface itself only asks for mutual refinement
-- (two inequalities) and includes monotonicity as an explicit side-condition.
-- This keeps BoundaryFix explicit and non-vacuous while leaving the core unchanged.
