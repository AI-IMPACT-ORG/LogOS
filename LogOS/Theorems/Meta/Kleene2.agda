{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Kleene2 where

-- Kleene’s second recursion theorem, in LogOS form.
--
-- In classical computability, SRT says: for any (total) computable operator f,
-- there exists a program e such that φₑ = φ_{f(e)}.
--
-- In LogOS, we isolate the *representation* assumption needed to talk about
-- “code operators” in a model-independent way:
--
--   `InternalHomWitness K` (a.k.a. `QuoteSubst⊑ K`)
--
-- This is the Lawvere-style fixed point interface already used to derive
-- diagonalisation and Löb. Here we re-expose it under the Kleene-2 name, with
-- two variants:
-- - preorder/lax form: mutual refinement (⊑ both ways)
-- - partial-order form: strict decoded meaning (`≃K`)

open import LogOS.Prelude
open import LogOS.Prelude using (Σ; _,_; _×_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary; BulkBoundaryPO)
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Eq using (module ForKernel)

open import LogOS.Theorems.Meta.Assumptions.Diagonal as Diag
  using
    ( InternalHomWitness
    ; lawvereFix
    ; lawvereFix≡
    ; lawvereDiag
    ; lawvereDiag≡
    ; lawvereDiag-⊑
    ; ⊑-lawvereDiag
    )

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  where

  open Kernel K

  -- Kleene-2 / SRT, preorder form:
  -- there exists a code fixed point up to mutual refinement at the boundary.
  Kleene2-⊑
    : InternalHomWitness K
    → (f : Code → Code)
    → Σ Code (λ s →
        ConPreorder._⊑_ (BulkBoundary.bnd BB) (decode s) (decode (f s))
      × ConPreorder._⊑_ (BulkBoundary.bnd BB) (decode (f s)) (decode s))
  Kleene2-⊑ = lawvereFix {K = K}

  -- Convenience: canonical fixed-point chooser (diagonal operator).
  diag : InternalHomWitness K → (Code → Code) → Code
  diag = lawvereDiag {K = K}

  diag-⊑ : (IH : InternalHomWitness K) (f : Code → Code)
         → ConPreorder._⊑_ (BulkBoundary.bnd BB) (decode (diag IH f)) (decode (f (diag IH f)))
  diag-⊑ = lawvereDiag-⊑ {K = K}

  ⊑-diag : (IH : InternalHomWitness K) (f : Code → Code)
         → ConPreorder._⊑_ (BulkBoundary.bnd BB) (decode (f (diag IH f))) (decode (diag IH f))
  ⊑-diag = ⊑-lawvereDiag {K = K}

  -- Kleene-2 / SRT, partial-order form:
  -- if the boundary preorder is antisymmetric, the fixed point is an equality.
  Kleene2-≡
    : BulkBoundaryPO BB
    → InternalHomWitness K
    → (f : Code → Code)
    → Σ Code (λ s → ForKernel._≃K_ K s (f s))
  Kleene2-≡ = lawvereFix≡ {K = K}

  diag-≡
    : BulkBoundaryPO BB
    → (IH : InternalHomWitness K)
    → (f : Code → Code)
    → ForKernel._≃K_ K (diag IH f) (f (diag IH f))
  diag-≡ po = lawvereDiag≡ {K = K} po
