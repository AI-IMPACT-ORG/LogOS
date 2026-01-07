{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
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

-- Default multi-port builder from a `BoundaryIO`: every role shares the same view.

defaultMultiBoundaryIOFromBoundaryIO
  : ∀ {ℓ} {Role : Set ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → MultiBoundaryIO Role Sig Q W BB H
defaultMultiBoundaryIOFromBoundaryIO {Role = Role} B =
  record
    { to∂    = λ _ w → BoundaryIO.to∂ B w
    ; from∂  = λ _ p → BoundaryIO.from∂ B p
    ; Sat∂   = λ _ p c → BoundaryIO.Sat∂ B p c
    ; sat-coh-role = λ _ w c → BoundaryIO.sat-coh B w c
    }

-- Default multi-port builder from a Kernel: every role shares the same view.

defaultMultiBoundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (Role : Set ℓ)
    (K : Kernel Sig Q)
  → MultiBoundaryIO Role Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
defaultMultiBoundaryIO {Sig = Sig} Role K =
  defaultMultiBoundaryIOFromBoundaryIO {Role = Role} (boundaryIO K)
  where
  open import LogOS.Kernel.Boundary using (boundaryIO)
