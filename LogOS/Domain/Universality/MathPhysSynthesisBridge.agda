{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.MathPhysSynthesisBridge where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ScaleOps using (ScaleOps)
open import LogOS.Kernel using (Kernel)

-- ============================================================================
-- MathPhysSynthesisBridge
--
-- Purpose: make the correspondence between the “observer/opacity” axiom surface
-- (`MathPhysSynthesis`) and standard physical information‑theory principles
-- explicit in *code*, using the existing LogOS universality/physics packs.
--
-- This file does not claim “experimentally confirmed” inside Agda; instead it
-- pins down the *exact formal shapes* of the principles that are commonly
-- treated as experimentally supported:
--
-- - Data Processing Inequality (DPI): classical information cannot increase
--   under admissible post‑processing.
-- - Landauer/2nd Law: irreversible (“merge”) evolution forces entropy increase
--   and yields Landauer‑style lower bounds.
-- - Non‑unitary / measurement capacity: extracting classical information is
--   mediated by a bounded number of non‑unitary events.
-- - Throughput bounds: irreversible events per unit physical time are bounded.
--
-- The key point for LogOS is that these principles naturally instantiate:
-- - “budgets live in a scale” (`QAdapter.Scale Q`) with an order `_≤s_`,
-- - “irreversibility/measurement” is countable and capacity‑bounded, and
-- - “opacity” results can be stated against any such budget, especially for
--   graded kernels where budgets are naturally quantale‑valued.
-- ============================================================================

import LogOS.Domain.Universality.DataProcessingInequality as DPI
import LogOS.Domain.Universality.NonUnitaryCapacity as NUC
import LogOS.Domain.Universality.SecondLaw as SL
import LogOS.Domain.Universality.InfoProcessingBounds as IPB
import LogOS.Domain.Universality.MeasurementCapacity as MC

import LogOS.Theorems.Meta.Landauer as Landauer
open import LogOS.Theorems.Meta.MathPhysSynthesis as MPS
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BSO
open import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO

-- ============================================================================
-- 1) Physical information theory principles (as explicit packs)
-- ============================================================================

record PhysicalInfoTheory {ℓ : Level}
                          (Sig : LogOSSignature ℓ)
                          (Q   : QAdapter ℓ)
                          : Set (lsuc (lsuc ℓ)) where
  field
    -- Classical information monotonicity (DPI) over an abstract observable carrier.
    --
    -- This is intentionally measure-theory free; it is the minimal shape needed
    -- by information‑bottleneck arguments.
    Obs : Set ℓ
    dpi : DPI.DPI Obs

    -- “Measurement/non‑unitary capacity”: information ≤ κ · (# non‑unitary events).
    nuc : NUC.NonUnitaryCapacity Sig Q

    -- “2nd law” layer: irreversible evolution forces entropy production.
    secondLaw : SL.SecondLawAssumptions Sig Q

    -- Throughput layer: merges/erasure events are bounded by time‑budget.
    throughput : IPB.ThroughputAssumptions Sig Q

    -- Operational interpretation of grades as step budgets.
    --
    -- This is the bridge used by the computational universality story
    -- (step semantics) and the complexity story (resource budgets) to talk to
    -- each other.
    ops : ScaleOps Q

-- Small derived facts that are used as “named correspondences”.
module DerivedPhys
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (P : PhysicalInfoTheory Sig Q)
  where
  open PhysicalInfoTheory P

  landauer : Landauer.LandauerAssumptions Sig Q
  landauer = SL.landauerFromLCU secondLaw

  nuc-info≤κ·nu
    : ∀ f → NUC.NonUnitaryCapacity.info nuc f
          ≤ℕ MC.mul (NUC.NonUnitaryCapacity.κ nuc)
                   (NUC.NonUnitaryCapacity.nuEvents nuc f)
  nuc-info≤κ·nu = NUC.NonUnitaryCapacity.info≤κ·nu nuc

  merges≤budget
    : ∀ f → IPB.ThroughputAssumptions.merges throughput f
          ≤ℕ IPB.ThroughputAssumptions.budget throughput
               (IPB.ThroughputAssumptions.ticks throughput f)
  merges≤budget = IPB.ThroughputAssumptions.merges≤budget throughput

-- ============================================================================
-- 2) Bridge point: physical budgets → opacity-style diagonal barriers
-- ============================================================================

-- The BudgetedSeparationOutput module already provides a general “within budget”
-- diagonal barrier that is:
-- - independent of decidability of the scale order (graded-kernel friendly), and
-- - stated purely at the code language level via `TruthDiagonalC`.
--
-- This is the exact place where “physical information theory” becomes an input:
-- take budgets in the physical scale `QAdapter.Scale Q`, ordered by `_≤s_`,
-- and interpret `costB` / `Bnd` using any experimentally motivated cost model
-- (entropy/energy/time/non-unitary events).

module OpacityFromPhysicalBudget
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {K   : Kernel Sig Q}
  (O   : SSO.SpectralSeparationOutput K)
  (C   : BSO.WitnessCost (SSO.SpectralSeparationOutput.Witness O))
  (Ops : ScaleOps Q)
  where
  -- “Physical scale” for budgets (e.g. energy/time/entropy-like), with order.
  B : Set ℓ
  B = QAdapter.Scale Q

  infix 4 _≤B_
  _≤B_ : B → B → Set ℓ
  _≤B_ = QAdapter._≤s_ Q

  module For = BSO.For O C

  -- Convert a scale-valued budget into a discrete (ℕ) step budget.
  --
  -- This is the intended “glue” to computational universality: it lets you
  -- phrase “within grade g” as “within N steps”, without choosing any specific
  -- machine model.
  steps≤ : B → ℕ
  steps≤ g = ScaleOps.steps Ops (ScaleOps.budget Ops g)

  -- General theorem (budget can live in `Scale`, order need not be decidable):
  --
  -- If you posit a diagonal principle for the budgeted “has separation within
  -- physical budget Bnd”, then no oracle can be total while staying within that
  -- budget on all inputs.
  --
  -- This is the “opacity lever”: physical budgeting assumptions are used only to
  -- justify the chosen `Bnd` and witness-cost model; the diagonal principle is
  -- the metalogical ingredient.
  module General
    (CB : For.WitnessCostB B)
    where
    open For
    module G = For.General B _≤B_ CB
    open G public

-- ============================================================================
-- 3) Direct observer-semantics correspondence (MathPhysSynthesis as “physics gate”)
-- ============================================================================

-- A small “use pattern”: to treat a *budgeted physical claim* as a LogOS truth
-- predicate, instantiate `MathPhysSynthesis` with `TruthK = WithinBudget`.
module MathPhysSynthesisAsPhysicalGate
  {ℓCode ℓDec ℓT : Level}
  (Code   : Set ℓCode)
  (Dec    : Set ℓDec)
  (decode : Code → Dec)
  (step   : Code → Code)
  (TruthK : Code → Set ℓT)
  (M : MPS.MathPhysSynthesis Code Dec decode step TruthK)
  where
  -- Re-export the observer-semantics surface bundled by `MathPhysSynthesis`.
  open MPS.MathPhysSynthesis M public
