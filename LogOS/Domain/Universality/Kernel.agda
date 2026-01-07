{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Kernel where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)

open import LogOS.Domain.Universality.Core
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Computation.Core
open import LogOS.Computation.FromKernel
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded

-- A Kernel whose Code is ToyUCode and whose Guarded step (Guard ∘ Body) is stepToyU.
-- (Toy universality core.)

-- Trivial signature and world
Sig : LogOSSignature lzero
Sig = record
  { sorts = record { Iface = ⊤ ; Cosp = ⊤ ; ∂Cosp = ⊤ }
  ; cospanOps = record { src = λ _ → tt ; tgt = λ _ → tt ; idC = λ _ → tt ; _∘C_ = λ _ _ → tt ; _⊕C_ = λ _ _ → tt ; _⊗C_ = λ _ _ → tt }
  ; boundaryOps = record { src∂ = λ _ → tt ; tgt∂ = λ _ → tt ; id∂ = λ _ → tt ; _∘∂_ = λ _ _ → tt ; _⊕∂_ = λ _ _ → tt ; _⊗∂_ = λ _ _ → tt ; from∂ = λ _ → tt ; to∂ = λ _ → tt }
  }

Q : QAdapter lzero
Q = trivialQAdapter

module W = Worlds Sig

HWorld : W.WorldH Q
HWorld = record { _≤ctx_ = λ _ _ → ⊤ ; WFlow = λ _ _ → tt ; wflow-refl = λ _ → tt ; wflow-trans = λ _ _ _ → tt }

-- Trivial poset and monoid on boundary constraints
conPoset : ConPoset lzero
conPoset = record { Con = ⊤ ; _⊑_ = λ _ _ → ⊤ ; refl = tt ; trans = λ _ _ → tt }

BB : BulkBoundary lzero
BB = record { bulk = conPoset ; bnd = conPoset }

MBnd : MonoidalPoset (BulkBoundary.bnd BB)
MBnd = record { _⊗_ = λ _ _ → tt ; I = tt ; mono⊗ = λ _ _ → tt }

-- Graded truth: in this toy kernel, grading is present but ignored (Flow is constant).
-- This is the intended lightweight upgrade path: existing ungraded constructions lift
-- to graded ones when a saturation/top grade is available.

module GT = Truth.GuardedCore {ℓ = lzero}

GTruth : GT.GradedClosure Q (BulkBoundary.bnd BB)
GTruth = record
  { Flow       = λ _ c → c
  ; mono       = λ {g} p → p
  ; mono-grade = λ _ _ → tt
  ; comp-lax   = λ _ _ _ → tt
  ; sat        = tt
  ; sat-top    = λ _ → tt
  ; infl-sat   = λ _ → tt
  ; idemp-sat  = λ _ → tt
  ; Th*        = tt
  ; Th*-fixed  = (tt , tt)
  }

-- GradedKernel with Code = ToyUCode and Guard = stepToyU

GUK : GradedKernel Sig Q
GUK = record
  { shape = record
      { HWorld = HWorld
      ; BB     = BB
      ; MBulk  = MBnd
      ; MBnd   = MBnd
      ; Holo   = record
          { core = record
              { ext = λ _ → tt
              ; bnd = λ _ → tt
              ; unit-lax = λ _ → tt
              ; counit-lax = λ _ → tt
              }
          ; ext-⊗-lax = λ _ _ → tt
          ; ext-I-lax = tt
          ; bnd-⊗-lax = λ _ _ → tt
          ; bnd-I-lax = tt
          }
      ; HTruth = record { Sat_H = λ _ _ → ⊤ ; mono-Con = λ _ _ → tt ; mono-ctx = λ _ _ → tt }
      ; HInv   = record { Inv_H = λ c → c ; infl = λ _ → tt ; idemp-lax = λ _ → tt }
      ; Sat_H_bnd = λ _ _ → ⊤
      ; sat-coh   = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Fml    = ⊤
      ; Strict = record { Sat_S = λ _ _ → ⊤ }
      ; TransH = λ _ → tt
      ; coh-LH = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Code   = ToyUCode
      ; encode = λ _ → ToyT (mkT 0 0)
      ; decode = λ _ → tt
      ; decode∘encode = λ { ttℓ → refl }
      ; Guard  = λ γ → stepToyU γ
      ; Body = λ γ → γ
      ; γ*           = ToyC (mkC 0)
      ; γ*-guard     = (tt , tt)
      ; reify        = λ _ → ToyT (mkT 0 0)
      ; reify-decode = λ _ → refl
      ; Body∂      = λ _ → tt
      ; body-decode = λ _ → refl
      }
  ; GTruth = GTruth
  ; step-grade   = tt
  ; guard-decode = λ _ → refl
  ; decode-γ*    = refl
  }

-- Derive Computation from the toy kernel and relate iterate to simulateToy

module FK = FromGradedKernel Sig Q GUK
UKComp : Computation (GradedKernel.Code GUK)
UKComp = FK.Comp

-- Helper projection of Step for clarity
StepUK : ToyUCode → ToyUCode
StepUK = Computation.Step UKComp

iterateUK : ℕ → ToyUCode → ToyUCode
iterateUK = iterate UKComp

-- iterateUK coincides with simulateToy from the universality core

iter-simulate : ∀ n u → iterateUK n u ≡ simulateToy n u
iter-simulate zero    u = refl
iter-simulate (suc n) u = iter-simulate n (stepToyU u)
