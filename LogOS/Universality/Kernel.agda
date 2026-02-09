{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Universality.Kernel where

open import LogOS.Prelude
open import LogOS.Prelude using (ℕ; zero; suc)

open import LogOS.Universality.Core
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Computation.Core
open import LogOS.Computation.FromKernel
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.API.Kernel.Graded

-- A Kernel whose Code is CoreUCode and whose Guarded step (Guard ∘ Body) is stepCoreU.
-- (Universality core.)

-- Minimal signature and world (observation contexts are explicit).
Sig : LogOSSignature lzero
Sig = record
  { sorts = record { Iface = ⊤ ; Cosp = ℕ ; ∂Cosp = ℕ }
  ; cospanOps = record
      { src = λ _ → tt
      ; tgt = λ _ → tt
      ; idC = λ _ → zero
      ; _∘C_ = λ _ _ → zero
      ; _⊕C_ = λ _ _ → zero
      ; _⊗C_ = λ _ _ → zero
      }
  ; boundaryOps = record
      { src∂ = λ _ → tt
      ; tgt∂ = λ _ → tt
      ; id∂ = λ _ → zero
      ; _∘∂_ = λ _ _ → zero
      ; _⊕∂_ = λ _ _ → zero
      ; _⊗∂_ = λ _ _ → zero
      ; from∂ = λ x → x
      ; to∂ = λ x → x
      }
  }

Q : QAdapter lzero
Q = trivialQAdapter

module W = Worlds Sig

HWorld : W.WorldH Q
HWorld = record { _≤ctx_ = λ _ _ → ⊤ ; WFlow = λ _ _ → tt ; wflow-refl = λ _ → tt ; wflow-trans = λ _ _ _ → tt }

-- Trivial preorder and monoid on boundary constraints
conPreorder : ConPreorder lzero
conPreorder = record { Con = ⊤ ; _⊑_ = λ _ _ → ⊤ ; refl = tt ; trans = λ _ _ → tt }

-- Explicit degeneracy witness: boundary order is top.
topOrderConPreorder : TopOrder conPreorder
topOrderConPreorder = record { top = λ _ _ → tt }

BB : BulkBoundary lzero
BB = record { bulk = conPreorder ; bnd = conPreorder }

MBnd : MonoidalOps (BulkBoundary.bnd BB)
MBnd = record { _⊗_ = λ _ _ → tt ; I = tt ; mono⊗ = λ _ _ → tt }

module HT = Truth.HomotypicalTruth Sig Q HWorld

HTruth : HT.HLayer BB
HTruth = record { Sat_H = λ _ _ → ⊤ ; mono-Con = λ _ _ → tt ; mono-ctx = λ _ _ → tt }

-- Explicit degeneracy witness: H-tier truth is vacuous (always satisfied).
vacuousHTruth : HT.VacuousHLayer HTruth
vacuousHTruth = record { satAll = λ _ _ → tt }

HInv : HT.Invariance BB
HInv = record { Inv_H = λ c → c ; infl = λ _ → tt ; idemp-lax = λ _ → tt }

-- Graded truth: in this kernel, grading is present but ignored (Flow is constant).
-- This is the intended lightweight upgrade path: existing ungraded constructions lift
-- to graded ones when a saturation/top grade is available.

module GT = Truth.GuardedCore {ℓ = lzero}

GTruthGraded : GT.GradedClosure Q (BulkBoundary.bnd BB)
GTruthGraded = record
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

-- GradedKernel with Code = CoreUCode and Guard = stepCoreU

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
      ; HTruth = HTruth
      ; HInv   = HInv
      ; Sat_H_bnd = λ _ _ → ⊤
      ; sat-coh   = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Fml    = ⊤
      ; Strict = record { Sat_S = λ _ _ → ⊤ }
      ; TransH = λ _ → tt
      ; coh-LH = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Code   = CoreUCode
      ; encode = λ _ → CoreT (mkT 0 0)
      ; decode = λ _ → tt
      ; Guard  = λ γ → stepCoreU γ
      ; Body = λ γ → γ
      ; γ*           = CoreC (mkC 0)
      ; reify        = λ _ → CoreT (mkT 0 0)
      ; Body∂      = λ _ → tt
      }
  ; shapeLaws = record
      { decode∘encode = λ { ttℓ → refl }
      ; γ*-guard      = (tt , tt)
      ; reify-decode  = λ _ → refl
      ; body-decode   = λ _ → refl
      }
  ; GTruth = GTruthGraded
  ; step-grade   = tt
  ; guard-decode = λ _ → refl
  ; decode-γ*    = refl
  }

-- Derive Computation from the kernel and relate iterate to simulateCoreU

module FK = FromGradedKernel Sig Q GUK
UKComp : Computation (GradedKernel.Code GUK)
UKComp = FK.Comp

-- Helper projection of Step for clarity
StepUK : CoreUCode → CoreUCode
StepUK = Computation.Step UKComp

iterateUK : ℕ → CoreUCode → CoreUCode
iterateUK = iterate UKComp

-- iterateUK coincides with simulateCoreU from the universality core

iter-simulate : ∀ n u → iterateUK n u ≡ simulateCoreU n u
iter-simulate zero    u = refl
iter-simulate (suc n) u = iter-simulate n (stepCoreU u)
