{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Landauer where

-- Landauer-style lower bound as a small, explicit assumption pack over a signature
-- and adapter. This keeps the Minimal/Kernal core unchanged and `--safe`, while
-- allowing models to opt in with a cost semantics and a predicate capturing
-- “bit erasure” (or any many-to-one effect you want to bound).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

-- Assumptions for a Landauer-style bound

record LandauerAssumptions {ℓ : Level}
                           (Sig : LogOSSignature ℓ)
                           (Q   : QAdapter ℓ)
                           : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  open QAdapter Q renaming (Scale to S; _≤s_ to _≤E_; _·_ to _⊙_; e to ε)
  field
    -- Distinguished minimal cost (abstract kT ln 2 unit)
    L     : S
    -- Program cost in the energy/Scale carrier
    cost  : Cosp → S
    -- Predicate capturing “bit erasure” (or any irreversible merge) at the program level
    Merges : Cosp → Set ℓ
    -- Core lower bound: any merge forces at least L units of cost
    merges→lower : ∀ f → Merges f → _≤E_ L (cost f)

-- Landauer lower bound theorem: immediate from the pack, kept as a named lemma.

landauer
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : LandauerAssumptions Sig Q)
    (f : LogOSSignature.Cosp Sig)
  → LandauerAssumptions.Merges A f
  → QAdapter._≤s_ Q (LandauerAssumptions.L A) (LandauerAssumptions.cost A f)
landauer A f pr = LandauerAssumptions.merges→lower A f pr

