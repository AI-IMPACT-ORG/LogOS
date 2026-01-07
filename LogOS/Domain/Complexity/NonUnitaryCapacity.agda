{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.NonUnitaryCapacity where

open import LogOS.Prelude

open import Data.Nat using (ℕ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

import LogOS.Domain.Complexity.LCUToLandauer as LCU
import LogOS.Domain.Complexity.MeasurementCapacity as MC

-- Semantic pivot: treat “measurement” and “forgetting/abstraction” uniformly as
-- *non-unitary classicalization events*.
--
-- The point is to let domains state softer assumptions:
--   “correctness forces global non-unitary effects”
-- rather than directly postulating a combinatorial merge-count lower bound.
--
-- This interface supports two styles of downstream arguments:
-- 1) capacity/throughput (info per event, events per time), and
-- 2) Landauer/2nd-law (energy/entropy per irreversible event).
--
-- A “classicalization event” is any step that is *not* locally unitary, i.e. it
-- cannot be modeled as an injective action on observables.

record NonUnitaryCapacity {ℓ : Level}
                          (Sig : LogOSSignature ℓ)
                          (Q   : QAdapter ℓ)
                          : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  field
    LCUA : LCU.LCUObsAssumptions Sig Q

    -- Count of non-unitary/classicalization events for a program.
    nuEvents : Cosp → ℕ

    -- “Classical information” associated to a program:
    -- extracted bits, entropy exported, descriptional commitment, etc.
    info : Cosp → ℕ

    -- Capacity bound: each non-unitary event can account for at most κ bits.
    κ : ℕ
    info≤κ·nu : ∀ f → MC._≤ℕ_ (info f) (MC.mul κ (nuEvents f))

    -- Reversibility preservation: locally unitary programs need no non-unitary events.
    unitary→nu0 : ∀ f → LCU.LCUObsAssumptions.LocalUnitary LCUA f → nuEvents f ≡ 0

-- Measurement is one instance of the above pivot.

measurementAsNonUnitary
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → MC.MeasurementCapacity Sig Q
    → NonUnitaryCapacity Sig Q
measurementAsNonUnitary {Sig = Sig} {Q = Q} cap =
  record
    { LCUA       = MC.MeasurementCapacity.LCUA cap
    ; nuEvents   = MC.MeasurementCapacity.meas cap
    ; info       = MC.MeasurementCapacity.info cap
    ; κ          = MC.MeasurementCapacity.κ cap
    ; info≤κ·nu  = MC.MeasurementCapacity.info≤κ·meas cap
    ; unitary→nu0 = MC.MeasurementCapacity.unitary→meas0 cap
    }
