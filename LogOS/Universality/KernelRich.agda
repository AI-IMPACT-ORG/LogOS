{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Universality.KernelRich where

open import LogOS.Prelude

open import LogOS.Universality.Core using (CoreUCode; CoreT; CoreC; CoreQ; CoreB; mkC; mkT; observeCore; canonCore)
open import LogOS.Syntax.Prop as Prop
open import LogOS.Universality.Kernel public using (Sig; Q; HWorld)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.API.Kernel
open import LogOS.Prelude using (ℕ)

-- A kernel over CoreUCode where boundary constraints are also CoreUCode and decode = id.
--
-- This is a deliberately *observer-shaped* model:
-- - the boundary preorder identifies codes that have the same observable;
-- - Flow is a canonicalization into an explicit “observable representative”.

module W = Worlds Sig

observe : CoreUCode → ℕ
observe = observeCore

canon : CoreUCode → CoreUCode
canon = canonCore

-- Constraints: both bulk and boundary are CoreUCode, ordered by observation equality
-- (`observe u ≡ observe v`).
conPreorderU : ConPreorder lzero
conPreorderU = record
  { Con = CoreUCode
  ; _⊑_ = λ u v → observe u ≡ observe v
  ; refl = refl
  ; trans = trans
  }

BB : BulkBoundary lzero
BB = record { bulk = conPreorderU ; bnd = conPreorderU }

-- Tensor ops on CoreUCode (arbitrary, monotone under observation equality).
MBulk : MonoidalOps (BulkBoundary.bulk BB)
MBulk = record
  { _⊗_ = λ x _ → x
  ; I = CoreC (mkC 0)
  ; mono⊗ = λ {x} {x'} {y} {y'} x⊑x' _ → x⊑x'
  }

MBnd : MonoidalOps (BulkBoundary.bnd BB)
MBnd = record
  { _⊗_ = λ x _ → x
  ; I = CoreT (mkT 0 0)
  ; mono⊗ = λ {x} {x'} {y} {y'} x⊑x' _ → x⊑x'
  }

-- Lax monoidal adjunction: identity on CoreUCode
Holo : LaxMonoidalAdjunction BB MBulk MBnd
Holo = record
  { core = record
      { ext = λ x → x
      ; bnd = λ x → x
      ; unit-lax = λ _ → refl
      ; counit-lax = λ _ → refl
      }
  ; ext-⊗-lax = λ _ _ → refl
  ; ext-I-lax = refl
  ; bnd-⊗-lax = λ _ _ → refl
  ; bnd-I-lax = refl
  }

-- Trivial H/G truth
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
HInv = record { Inv_H = λ c → c ; infl = λ _ → refl ; idemp-lax = λ _ → refl }

GTierU : GTier Q (BulkBoundary.bnd BB)
GTierU =
  record
    { Step      = ⊤
    ; step      = tt
    ; sat       = tt
    ; Flow      = λ _ c → canon c
    ; mono      = λ {g} le → le
    ; infl-sat  = λ _ → refl
    ; idemp-sat = λ _ → refl
    ; Th*       = CoreT (mkT 0 0)
    ; Th*-fixed = (refl , refl)
    }

-- Kernel with Code = CoreUCode and decode = id
UKR : Kernel Sig Q
UKR = record
  { shape = record
      { HWorld = HWorld
      ; BB = BB
      ; MBulk = MBulk
      ; MBnd = MBnd
      ; Holo = Holo
      ; HTruth = HTruth
      ; HInv = HInv
      ; Sat_H_bnd = λ _ _ → ⊤
      ; sat-coh = λ _ _ → Prop.↔-refl
      ; Fml = ℕ
      ; Strict = record { Sat_S = λ _ _ → ⊤ }
      ; TransH = λ n → CoreC (mkC n)
      ; coh-LH = λ _ _ → Prop.↔-refl
      ; Code = CoreUCode
      ; encode = λ γ → γ
      ; decode = λ γ → γ
      ; Guard = canon
      ; Body = λ γ → γ
      ; γ* = CoreT (mkT 0 0)
      ; reify = λ γ → γ
      ; Body∂ = λ c → c
      }
  ; shapeLaws = record
      { decode∘encode = λ _ → refl
      ; γ*-guard      = (refl , refl)
      ; reify-decode  = λ _ → refl
      ; body-decode   = λ _ → refl
      }
  ; G = GTierU
  ; guard-decode = λ _ → refl
  ; decode-γ*    = refl
  }
