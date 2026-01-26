{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.SpectralSeparation where

open import LogOS.Prelude
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo

-- Local addition on ℕ (for indexing tails of approximants)
open import LogOS.Prelude.Nat using (ℕ; zero; suc; _+_)

-- Spectrally separated Flow assumptions at the boundary: a predicate Pred
-- describing a “separation region” that is closed under Flow and contractive
-- there, together with a witness that some approximant reaches the region.

record SpectralSeparationSpec {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                              (K : Kernel Sig Q)
                              (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO)
                                        (BulkBoundary.bnd (Kernel.BB K)))
                              (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst)
                                        (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
                              : Set (lsuc ℓ) where
  private
    module GT = Truth.GuardedTruth Sig Q
    open ConPreorder (BulkBoundary.bnd (Kernel.BB K)) using (Con; _⊑_)
    open GT.GuardedClosure (Kernel.GTruth K) renaming (Th* to Th⋆)
    open GT.FiniteFirst FF renaming (approxS to A)
    F = Endo.fn (Flow-Endo K)
  field
    Pred        : Con → Set ℓ
    closed      : ∀ {c} → Pred c → Pred (F c)
    contractive : ∀ {c} → Pred c → _⊑_ (F c) c
    reaches     : Σ ℕ (λ n → Pred (A n))

-- Consequences of SpectralSeparationSpec: a concrete approximant is a fixed point
-- (up to ⊑), and bounds relating that approximant to Th⋆. Under antisymmetry
-- (partial order) these become equalities.

record SpectralSeparationResults {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                (K : Kernel Sig Q)
                                (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO)
                                          (BulkBoundary.bnd (Kernel.BB K)))
                                (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst)
                                          (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
                                (SS   : SpectralSeparationSpec K ωCPO FF)
                                : Set (lsuc ℓ) where
  private
    module GT = Truth.GuardedTruth Sig Q
    open ConPreorder (BulkBoundary.bnd (Kernel.BB K)) using (Con; _⊑_)
    open GT.GuardedClosure (Kernel.GTruth K) renaming (Th* to Th⋆)
    open GT.OmegaCPO ωCPO
    open GT.FiniteFirst FF renaming (approxS to A; Th⋆-as-sup to supineq)
    open SpectralSeparationSpec SS
    F = Endo.fn (Flow-Endo K)
  field
    n* : ℕ
    fixed-ineq : (_⊑_ (F (A n*)) (A n*)) × (_⊑_ (A n*) (F (A n*)))
    Th⋆-bounds : (_⊑_ Th⋆ (A n*)) × (_⊑_ (A n*) Th⋆)

-- Inequality construction: use contractiveness on the separation region to get
-- F(A n) ⊑ A n, inflation to get A n ⊑ F(A n), μ-induction to show Th⋆ ⊑ A n,
-- and the approximant supremum characterization to show A n ⊑ Th⋆.

spectral-separation-inequalities
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO)
              (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst)
              (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
    (SS   : SpectralSeparationSpec K ωCPO FF)
  → SpectralSeparationResults K ωCPO FF SS
spectral-separation-inequalities {Sig = Sig}{Q = Q}{K = K} ωCPO FF SS =
  record { n* = n ; fixed-ineq = (F≤A , A≤F) ; Th⋆-bounds = (Th⋆≤A , A≤Th⋆) }
  where
    module GT = Truth.GuardedTruth Sig Q
    infix 4 _⊑b_
    _⊑b_ = ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
    open GT.GuardedClosure (Kernel.GTruth K) renaming (Th* to Th⋆)
    open GT.OmegaCPO ωCPO
    open GT.FiniteFirst FF renaming (approxS to A; Th⋆-as-sup to supineq)
    open SpectralSeparationSpec SS
    F = Endo.fn (Flow-Endo K)

    n : ℕ
    n = proj₁ reaches

    hit : Pred (A n)
    hit = proj₂ reaches

    -- Fixed-point inequalities at A n
    F≤A : _⊑b_ (F (A n)) (A n)
    F≤A = contractive hit

    A≤F : _⊑b_ (A n) (F (A n))
    A≤F = id≤Flow K (A n)

    -- μ-induction gives Th⋆ ≤ A n from F(A n) ⊑ A n
    Th⋆≤A : _⊑b_ Th⋆ (A n)
    Th⋆≤A = GT.μ-induction (Kernel.GTruth K) ωCPO FF (A n) F≤A

    -- A n ≤ Th⋆ via Th⋆-as-sup and the fact A n is an approximant
    sup≤ : _⊑b_ (supω A) Th⋆
    sup≤ = snd supineq

    ubA : _⊑b_ (A n) (supω A)
    ubA = ub A n

    A≤Th⋆ : _⊑b_ (A n) Th⋆
    A≤Th⋆ = ConPreorder.trans (BulkBoundary.bnd (Kernel.BB K)) ubA sup≤

-- Textbook alias: “finite convergence” from a contractive/closed region.
-- The result exposes a concrete approximant A n that is a fixed point (up to ⊑)
-- and bounds Th⋆ between it.

finite-convergence-inequalities = spectral-separation-inequalities

-- Under antisymmetry on the boundary preorder (hence a poset), the bounds give equalities.

spectral-separation-equalities
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (po  : BulkBoundaryPO (Kernel.BB K))
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO)
              (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst)
              (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
    (SS   : SpectralSeparationSpec K ωCPO FF)
  → Σ ℕ (λ n →
        (Endo.fn (Flow-Endo K)
           (Truth.GuardedCore.FiniteFirst.approxS FF n))
        ≡
        (Truth.GuardedCore.FiniteFirst.approxS FF n)
        ×
        (Th⋆K K)
        ≡
        (Truth.GuardedCore.FiniteFirst.approxS FF n))
spectral-separation-equalities {Sig = Sig}{Q = Q}{K = K} po ωCPO FF SS =
  (n* , (FAn≡An , Th⋆≡An))
  where
    res = spectral-separation-inequalities ωCPO FF SS
    n*  = SpectralSeparationResults.n* res
    module GT = Truth.GuardedTruth Sig Q
    open ConPreorder (BulkBoundary.bnd (Kernel.BB K)) using (Con; _⊑_)
    open BulkBoundaryPO po using (po-bnd)
    open PartialOrder (po-bnd) using (antisym)
    open GT.GuardedClosure (Kernel.GTruth K) renaming (Th* to Th⋆)
    open GT.FiniteFirst FF renaming (approxS to A)
    F = Endo.fn (Flow-Endo K)

    F≤A : _⊑_ (F (A n*)) (A n*)
    F≤A = fst (SpectralSeparationResults.fixed-ineq res)

    A≤F : _⊑_ (A n*) (F (A n*))
    A≤F = snd (SpectralSeparationResults.fixed-ineq res)

    Th⋆≤A : _⊑_ Th⋆ (A n*)
    Th⋆≤A = fst (SpectralSeparationResults.Th⋆-bounds res)

    A≤Th⋆ : _⊑_ (A n*) Th⋆
    A≤Th⋆ = snd (SpectralSeparationResults.Th⋆-bounds res)

    FAn≡An : F (A n*) ≡ A n*
    FAn≡An = antisym F≤A A≤F

    Th⋆≡An : Th⋆ ≡ A n*
    Th⋆≡An = antisym Th⋆≤A A≤Th⋆

-- Textbook alias: finite convergence with equality under antisymmetry.

finite-convergence-equalities = spectral-separation-equalities
