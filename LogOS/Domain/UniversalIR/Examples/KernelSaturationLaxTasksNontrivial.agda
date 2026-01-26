{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.KernelSaturationLaxTasksNontrivial where

-- A “nontrivial” instance of `KernelBoundaryTasks` where the boundary preorder is
-- genuinely non-symmetric, so the kernel-induced lax simulation is strict.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter; trivialQAdapter)
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Adjunction using (MonoidalOps; LaxMonoidalAdjunction)
import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel using (Kernel)
open import LogOS.Syntax.Prop as Prop

import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Computation.KernelBoundaryTasks

open import LogOS.Prelude.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ)

-- --------------------------------------------------------------------------
-- A tiny kernel with boundary constraints = ℕ ordered by ≤, and Flow enforcing
-- a minimal “stable truth” of 1 (so 0 is strictly below its saturation).

private
  Flowℕ : ℕ → ℕ
  Flowℕ zero    = suc zero
  Flowℕ (suc n) = suc n

  Flowℕ-mono : ∀ {m n : ℕ} → m ≤ℕ n → Flowℕ m ≤ℕ Flowℕ n
  Flowℕ-mono {zero}  {zero}  _  = ≤ℕ-refl
  Flowℕ-mono {zero}  {suc _} _  = s≤s z≤n
  Flowℕ-mono {suc _} {zero}  ()
  Flowℕ-mono {suc _} {suc _} le = le

  Flowℕ-infl : ∀ n → n ≤ℕ Flowℕ n
  Flowℕ-infl zero    = z≤n
  Flowℕ-infl (suc _) = ≤ℕ-refl

  Flowℕ-idemp≤ : ∀ n → Flowℕ (Flowℕ n) ≤ℕ Flowℕ n
  Flowℕ-idemp≤ zero    = ≤ℕ-refl
  Flowℕ-idemp≤ (suc _) = ≤ℕ-refl

  Thℕ : ℕ
  Thℕ = suc zero

Sig : LogOSSignature lzero
Sig = record
  { sorts = record { Iface = ⊤ ; Cosp = ⊤ ; ∂Cosp = ⊤ }
  ; cospanOps = record
      { src = λ _ → tt
      ; tgt = λ _ → tt
      ; idC = λ _ → tt
      ; _∘C_ = λ _ _ → tt
      ; _⊕C_ = λ _ _ → tt
      ; _⊗C_ = λ _ _ → tt
      }
  ; boundaryOps = record
      { src∂ = λ _ → tt
      ; tgt∂ = λ _ → tt
      ; id∂ = λ _ → tt
      ; _∘∂_ = λ _ _ → tt
      ; _⊕∂_ = λ _ _ → tt
      ; _⊗∂_ = λ _ _ → tt
      ; from∂ = λ _ → tt
      ; to∂ = λ _ → tt
      }
  }

Q : QAdapter lzero
Q = trivialQAdapter

module W = Worlds Sig

HWorld : W.WorldH Q
HWorld =
  record
    { _≤ctx_ = λ _ _ → ⊤
    ; WFlow  = λ _ _ → tt
    ; wflow-refl  = λ _ → tt
    ; wflow-trans = λ _ _ _ → tt
    }

conPreorderℕ : ConPreorder lzero
conPreorderℕ =
  record
    { Con   = ℕ
    ; _⊑_   = _≤ℕ_
    ; refl  = ≤ℕ-refl
    ; trans = trans≤ℕ
    }

BB : BulkBoundary lzero
BB = record { bulk = conPreorderℕ ; bnd = conPreorderℕ }

M : MonoidalOps conPreorderℕ
M =
  record
    { _⊗_   = λ x _ → x
    ; I     = zero
    ; mono⊗ = λ x≤x' _ → x≤x'
    }

Holo : LaxMonoidalAdjunction BB M M
Holo =
  record
    { core = record
        { ext = λ x → x
        ; bnd = λ x → x
        ; unit-lax   = λ _ → ≤ℕ-refl
        ; counit-lax = λ _ → ≤ℕ-refl
        }
    ; ext-⊗-lax = λ _ _ → ≤ℕ-refl
    ; ext-I-lax = ≤ℕ-refl
    ; bnd-⊗-lax = λ _ _ → ≤ℕ-refl
    ; bnd-I-lax = ≤ℕ-refl
    }

module HT = Truth.HomotypicalTruth Sig Q HWorld

HTruth : HT.HLayer BB
HTruth =
  record
    { Sat_H = λ _ _ → ⊤
    ; mono-Con = λ _ _ → tt
    ; mono-ctx = λ _ _ → tt
    }

-- Explicit degeneracy witness: H-tier truth is vacuous (always satisfied).
vacuousHTruth : HT.VacuousHLayer HTruth
vacuousHTruth = record { satAll = λ _ _ → tt }

HInv : HT.Invariance BB
HInv = record { Inv_H = λ c → c ; infl = λ _ → ≤ℕ-refl ; idemp-lax = λ _ → ≤ℕ-refl }

module ST = Truth.StrictTruth Sig

Strict : ST.StrictLayer ⊤
Strict = record { Sat_S = λ _ _ → ⊤ }

module GT = Truth.GuardedCore {ℓ = lzero}

GTruth : GT.GuardedClosure conPreorderℕ
GTruth =
  record
    { Flow = Flowℕ
    ; mono = Flowℕ-mono
    ; infl = Flowℕ-infl
    ; idemp-lax = Flowℕ-idemp≤
    ; Th* = Thℕ
    ; Th*-fixed = (≤ℕ-refl , ≤ℕ-refl)
    }

Kℕ : Kernel Sig Q
Kℕ =
  record
    { shape = record
        { HWorld = HWorld
        ; BB     = BB
        ; MBulk  = M
        ; MBnd   = M
        ; Holo   = Holo
        ; HTruth = HTruth
        ; HInv   = HInv
        ; Sat_H_bnd = λ _ _ → ⊤
        ; sat-coh = λ _ _ → Prop.↔-refl
        ; Fml    = ⊤
        ; Strict = Strict
        ; TransH = λ _ → zero
        ; coh-LH = λ _ _ → Prop.↔-refl
        ; Code   = ℕ
        ; encode = λ c → c
        ; decode = λ γ → γ
        ; Guard  = Flowℕ
        ; Body   = λ γ → γ
        ; γ*     = Thℕ
        ; reify  = λ γ → γ
        ; Body∂  = λ c → c
        }
    ; GTruth = GTruth
    ; laws = record
        { shapeLaws = record
            { decode∘encode = λ _ → refl
            ; γ*-guard      = (≤ℕ-refl , ≤ℕ-refl)
            ; reify-decode  = λ _ → refl
            ; body-decode   = λ _ → refl
            }
        ; mono-Body∂    = λ le → le
        ; mono-Flow     = Flowℕ-mono
        ; guard-decode  = λ _ → refl
        ; decode-γ*     = refl
        }
    }

-- --------------------------------------------------------------------------
-- Lax kernel saturation: raw boundary evolution factors through saturation,
-- but not conversely (strictness witness).

module K = ForKernel Kℕ

raw≤sat-step₀
  : Cat.Process._⊑_ K.SatBoundaryProcess (K.TRaw.execFrom 1 zero) (K.TSat.execFrom 1 zero)
raw≤sat-step₀ = K.execFrom≤sat 1 zero

sat≰raw-step₀
  : ¬ Cat.Process._⊑_ K.SatBoundaryProcess (K.TSat.execFrom 1 zero) (K.TRaw.execFrom 1 zero)
sat≰raw-step₀ ()
