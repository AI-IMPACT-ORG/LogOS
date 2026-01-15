{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.KernelRich where

open import LogOS.Prelude

open import LogOS.Domain.Universality.Core
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel

-- A kernel over CoreUCode where boundary constraints are also CoreUCode and decode = id.
--
-- This is a deliberately *observer-shaped* model:
-- - the boundary preorder identifies codes that have the same observable;
-- - Flow is a canonicalization into an explicit “observable representative”.

-- Signature and adapter as in the simple universality kernel
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

-- Observable extracted from code (the “measured” part).
observe : CoreUCode → ℕ
observe (CoreT t) = reg t
observe (CoreC c) = size c
observe (CoreQ q) = gates q
observe (CoreB b) = gas b

-- Canonical representative for the observable part.
--
-- We pick the Church branch to represent the “read-out” uniformly.
canon : CoreUCode → CoreUCode
canon u = CoreC (mkC (observe u))

-- Constraints: both bulk and boundary are CoreUCode, ordered by observational equivalence.
conPosetU : ConPoset lzero
conPosetU = record
  { Con = CoreUCode
  ; _⊑_ = λ u v → observe u ≡ observe v
  ; refl = refl
  ; trans = trans
  }

BB : BulkBoundary lzero
BB = record { bulk = conPosetU ; bnd = conPosetU }

-- Monoidal structures on CoreUCode (arbitrary, monotone under ⊤-preorder)
MBulk : MonoidalPoset (BulkBoundary.bulk BB)
MBulk = record
  { _⊗_ = λ x _ → x
  ; I = CoreC (mkC 0)
  ; mono⊗ = λ {x} {x'} {y} {y'} x⊑x' _ → x⊑x'
  }

MBnd : MonoidalPoset (BulkBoundary.bnd BB)
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
HTruth = record { Sat_H = λ _ _ → ⊤ ; mono-Con = λ _ _ → tt ; mono-ctx = λ _ _ → tt }

HInv : HT.Invariance BB
HInv = record { Inv_H = λ c → c ; infl = λ _ → refl ; idemp-lax = λ _ → refl }

module GT = Truth.GuardedTruth Sig Q
GTruth : GT.GuardedClosure (BulkBoundary.bnd BB)
GTruth = record
  { Flow = canon
  ; mono = λ p → p
  ; infl = λ _ → refl
  ; idemp-lax = λ _ → refl
  ; Th* = CoreT (mkT 0 0)
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
      ; sat-coh = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Fml = ⊤
      ; Strict = record { Sat_S = λ _ _ → ⊤ }
      ; TransH = λ _ → CoreT (mkT 0 0)
      ; coh-LH = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Code = CoreUCode
      ; encode = λ γ → γ
      ; decode = λ γ → γ
      ; Guard = canon
      ; Body = λ γ → γ
      ; γ* = CoreT (mkT 0 0)
      ; reify = λ γ → γ
      ; Body∂ = λ c → c
      }
  ; GTruth = GTruth
  ; laws = record
      { shapeLaws = record
          { decode∘encode = λ _ → refl
          ; γ*-guard      = (refl , refl)
          ; reify-decode  = λ _ → refl
          ; body-decode   = λ _ → refl
          }
      ; mono-Body∂    = λ {c} {d} le → le
      ; mono-Flow     = λ {c} {d} le →
                          Truth.GuardedCore.GuardedClosure.mono GTruth {c = c} {c' = d} le
      ; guard-decode  = λ _ → refl
      ; decode-γ*     = refl
      }
  }
