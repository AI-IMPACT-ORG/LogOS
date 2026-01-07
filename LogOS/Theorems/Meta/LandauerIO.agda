{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.LandauerIO where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Boundary.IO
open import LogOS.Minimal.Truth as Truth

-- A boundary‑I/O flavored Landauer pack: energy carrier from QAdapter, a program
-- cost `Cosp → Scale`, subadditive bounds for composition/tensor in the chosen
-- monoid, and a merges predicate at the program level (defined by the model).

record LandauerIOAssumptions {ℓ : Level}
                             (Sig : LogOSSignature ℓ)
                             (Q   : QAdapter ℓ)
                             (W   : Worlds.WorldH Sig Q)
                             (BB  : BulkBoundary ℓ)
                             (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                             (B   : BoundaryIO Sig Q W BB H)
                             : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  open QAdapter Q renaming (Scale to S; _≤s_ to _≤E_; _·_ to _⊙_; e to ε)
  open BoundaryIO B
  field
    L       : S
    cost    : Cosp → S
    -- Subadditivity (lax) with respect to the chosen monoid on Scale
    cost-comp   : ∀ (f g : Cosp) → _≤E_ (cost f ⊙ cost g) (cost (g ∘C f))
    cost-tensor : ∀ (f g : Cosp) → _≤E_ (cost f ⊙ cost g) (cost (f ⊗C g))
    cost-id     : ∀ (i : Iface) → _≤E_ ε (cost (idC i))
    -- Model-supplied merges predicate
    MergesIO : Cosp → Set ℓ
    merges→lower : ∀ (f : Cosp) → MergesIO f → _≤E_ L (cost f)

-- Core Landauer inequality (boundary I/O context)

landauer-io
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (A : LandauerIOAssumptions Sig Q W BB H B)
    (f : LogOSSignature.Cosp Sig)
  → LandauerIOAssumptions.MergesIO A f
  → QAdapter._≤s_ Q (LandauerIOAssumptions.L A) (LandauerIOAssumptions.cost A f)
landauer-io B A f pr = LandauerIOAssumptions.merges→lower A f pr

-- Composition/tensor helper inequalities packaged with LandauerIO

comp-bound
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (A : LandauerIOAssumptions Sig Q W BB H B)
    (f g : LogOSSignature.Cosp Sig)
  → QAdapter._≤s_ Q (QAdapter._·_ Q ((LandauerIOAssumptions.cost A) f) ((LandauerIOAssumptions.cost A) g))
                   ((LandauerIOAssumptions.cost A) (LogOSSignature._∘C_ Sig g f))
comp-bound B A f g = LandauerIOAssumptions.cost-comp A f g

tensor-bound
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (A : LandauerIOAssumptions Sig Q W BB H B)
    (f g : LogOSSignature.Cosp Sig)
  → QAdapter._≤s_ Q (QAdapter._·_ Q ((LandauerIOAssumptions.cost A) f) ((LandauerIOAssumptions.cost A) g))
                   ((LandauerIOAssumptions.cost A) (LogOSSignature._⊗C_ Sig f g))
tensor-bound B A f g = LandauerIOAssumptions.cost-tensor A f g
