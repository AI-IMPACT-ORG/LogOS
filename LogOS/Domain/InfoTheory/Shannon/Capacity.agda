{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.InfoTheory.Shannon.Capacity where

open import LogOS.Prelude hiding (_+_; _*_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; _,_)

open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Domain.InfoTheory.Shannon.Facts
import LogOS.Domain.InfoTheory.Shannon.Core as Core
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- Channel capacity and coding theorem interface (finite case).
--
-- This is intentionally a *pack*: we do not attempt to rebuild the large-deviation
-- machinery needed for Shannon’s coding theorem. Instead we provide:
-- 1) a definitional “mutual information” expression for finite kernels, and
-- 2) a coding-theorem interface that can be instantiated by a concrete model.

module For (F : ShannonFacts) where
  open ShannonFacts F public
  module C = Core.For F
  open C using (Dist; Kernel; push; H; KL)

  -- Mutual information of an input distribution `P` passed through a channel/kernel `K`.
  --
  -- We use the “joint vs product” KL form, but written as a nested finite sum
  -- to avoid flattening `Fin m × Fin n`.
  I : ∀ {m n : ℕ} → Kernel m n → Dist m → ℝ
  I {m} {n} K P =
    sum (λ i →
      sum (λ j →
        klTerm
          (Dist.p P i * Kernel.K K i j)
          (Dist.p P i * push K P j)))

  -- A capacity interface: `Capacity K` is the (operationally) achievable maximum rate,
  -- and it upper-bounds the mutual information of any single-shot input distribution.
  record CapacityFacts : Set₁ where
    field
      Capacity : ∀ {m n : ℕ} → Kernel m n → ℝ

      -- The “math” side: mutual information is always bounded by capacity.
      I≤Capacity : ∀ {m n : ℕ} (K : Kernel m n) (P : Dist m) → I K P ≤ Capacity K

      -- The “comp/ops” side: an abstract achievability notion for rates.
      Achievable : ∀ {m n : ℕ} → Kernel m n → ℝ → Set

      -- Coding theorem interface (finite block coding abstracted away):
      -- - rates below capacity are achievable;
      -- - rates above capacity are not.
      achievable≤ : ∀ {m n : ℕ} (K : Kernel m n) (R : ℝ) → R ≤ Capacity K → Achievable K R
      converse≥   : ∀ {m n : ℕ} (K : Kernel m n) (R : ℝ) → Capacity K ≤ R → ¬ (Achievable K R)

-- Standard “quartet” wrapper.
module QuartetCapacity where
  record Assumptions : Set₁ where
    field
      facts : ShannonFacts
      cap   : For.CapacityFacts facts

  private
    module With (A : Assumptions) where
      F = Assumptions.facts A
      module M = For F
      open M public
      open M.CapacityFacts (Assumptions.cap A) public

  Claim : Assumptions → Set₁
  Claim A =
    let module W = With A in
    let open W in
    ∀ {m n : ℕ} (K : Core.For.Kernel W.F m n) (P : Core.For.Dist W.F m) →
      I K P ≤ Capacity K

  module Q = Quartet.Make Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : (A : Assumptions) → Pack
  mkPack A =
    Q.mkPack
      (λ A → let module W = With A in W.I≤Capacity)
      A
