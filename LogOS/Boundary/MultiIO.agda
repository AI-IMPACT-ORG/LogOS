{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.MultiIO where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.IO
open import LogOS.Kernel

-- Role-indexed (multi-port) Boundary I/O. Each role exposes its own view.

record MultiBoundaryIO {ℓ : Level}
                       (Role : Set ℓ)
                       (Sig  : LogOSSignature ℓ)
                       (Q    : QAdapter ℓ)
                       (W    : Worlds.WorldH Sig Q)
                       (BB   : BulkBoundary ℓ)
                       (H    : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                       : Set (lsuc ℓ) where
  open LogOSSignature Sig
  module HT = Truth.HomotypicalTruth Sig Q W
  open BulkBoundary BB
  field
    to∂    : Role → Cosp → ∂Cosp
    from∂  : Role → ∂Cosp → Cosp
    Sat∂   : Role → ∂Cosp → Con_bnd → Set ℓ
    sat-coh-role : ∀ r (w : Cosp) (c : Con_bnd)
                 → Prop._↔_ (HT.HLayer.Sat_H H w c)
                             (Sat∂ r (to∂ r w) c)

-- Default multi-port builder from a Kernel: every role shares the same view.

defaultMultiBoundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (Role : Set ℓ)
    (K : Kernel Sig Q)
  → MultiBoundaryIO Role Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
defaultMultiBoundaryIO {Sig = Sig} Role K = record
  { to∂    = λ _ w → bnd w
  ; from∂  = λ _ p → ext p
  ; Sat∂   = λ _ p c → Kernel.Sat_H_bnd K p c
  ; sat-coh-role = λ _ w c → Kernel.sat-coh K w c
  }
  where
  open LogOSSignature Sig
