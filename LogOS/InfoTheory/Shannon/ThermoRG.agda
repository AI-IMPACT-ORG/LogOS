{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.InfoTheory.Shannon.ThermoRG where

open import LogOS.Prelude hiding (_+_; _*_)

open import LogOS.Prelude using (ℕ)

open import LogOS.Syntax.Prop using (¬_)

open import LogOS.InfoTheory.Shannon.Facts
import LogOS.InfoTheory.Shannon.Core as Core
import LogOS.Theorems.Meta.ApplicationKit as AppKit

-- “RG flow as coarse-graining” + “Landauer as entropy production” scaffold.
--
-- This is intentionally an *application bridge pack*:
-- - the Shannon layer lives in `ShannonFacts` (ℝ, ln/exp, log-sum, …),
-- - the physics layer (energy/cost) can live in a prequantale scale elsewhere,
-- - and this pack only states the minimal glue data/axioms needed to connect them.

module For (F : ShannonFacts) where
  open ShannonFacts F public
  module C = Core.For F
  open C using (Dist; Kernel; H; pushDist)

  record RGFacts : Set₁ where
    field
      n  : ℕ
      RG : Kernel n n

      -- “Coarse-graining increases entropy”: H(P) ≤ H(RG⋆P).
      H-mono : ∀ P → H P ≤ H (pushDist RG P)

      -- A designated entropy production witness (kept abstract to avoid subtraction).
      EntropyProduction : Dist n → ℝ

      -- Bookkeeping: the entropy production is exactly the entropy gap (in whatever
      -- normalization your model uses).
      H+EP≡H′ : ∀ P → (H P + EntropyProduction P) ≡ H (pushDist RG P)

  -- Landauer-style interface at the Shannon layer:
  -- a cost functional that lower-bounds entropy production (up to a constant).
  record LandauerShannonFacts (RG : RGFacts) : Set₁ where
    open RGFacts RG
    field
      Cost : Dist n → ℝ
      L    : ℝ

      -- Minimal bound: entropy production implies a cost.
      --
      -- Intended reading: `Cost` is “dissipation/irreversibility budget” and `L`
      -- is the unit (kT ln 2 in physics units).
      EP→Cost : ∀ P → (EntropyProduction P * L) ≤ Cost P

-- Standard “quartet” wrapper.
module QuartetThermoRG where
  record Assumptions : Set₁ where
    field
      facts : ShannonFacts
      rg    : For.RGFacts facts
      land  : For.LandauerShannonFacts facts rg

  private
    module With (A : Assumptions) where
      F = Assumptions.facts A
      module M = For F
      open M public
      open M.RGFacts (Assumptions.rg A) public
      open M.LandauerShannonFacts (Assumptions.land A) public

  Claim : Assumptions → Set₁
  Claim A =
    let module W = With A in
    let open W in
    ∀ P → (EntropyProduction P * L) ≤ Cost P

  derive : (A : Assumptions) → Claim A
  derive A = let module W = With A in W.EP→Cost

  module Q = AppKit.MakeDerived Assumptions Claim derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
