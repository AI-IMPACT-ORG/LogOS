{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.MeasurementCapacity where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ; ≤ℕ-refl; weakenRight) public

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.Domain.Universality.LCUToLandauer as LCU

-- A LogOS-native “measurement capacity” pack:
-- it bounds how much *classical information* can be extracted (classicalized)
-- per local event, under locality/causality constraints.
--
-- This stays compatible with reversible computation:
-- unitary/reversible dynamics can run arbitrarily long; only classicalization is charged.

-- Addition recursing on the *right* argument (so monotonicity proofs are clean).

plusR : ℕ → ℕ → ℕ
plusR a zero    = a
plusR a (suc n) = suc (plusR a n)

-- “Extractable classical info” is abstracted as a natural number.
-- Models can instantiate this with (log of) distinguishable outcomes, mutual information, etc.

-- Multiplication on naturals, using `plusR`.

mul : ℕ → ℕ → ℕ
mul zero    _ = zero
mul (suc m) n = plusR n (mul m n)

-- Monotonicity of addition and multiplication w.r.t. ≤ℕ (needed for time/throughput bridges).

monoPlusL : ∀ {a b} → a ≤ℕ b → ∀ c → plusR a c ≤ℕ plusR b c
monoPlusL ab zero = ab
monoPlusL ab (suc c) = s≤s (monoPlusL ab c)

lePlusR : ∀ a c → a ≤ℕ plusR a c
lePlusR a zero = ≤ℕ-refl
lePlusR a (suc c) = weakenRight (lePlusR a c)

monoPlusR : ∀ {c d} → c ≤ℕ d → ∀ a → plusR a c ≤ℕ plusR a d
monoPlusR {d = d} z≤n a = lePlusR a d
monoPlusR (s≤s cd) a = s≤s (monoPlusR cd a)

monoMul : ∀ k {a b} → a ≤ℕ b → mul k a ≤ℕ mul k b
monoMul zero ab = z≤n
monoMul (suc k) {a = a} {b = b} ab =
  trans≤ℕ
    (monoPlusL ab (mul k a))
    (monoPlusR (monoMul k ab) b)

record MeasurementCapacity {ℓ : Level}
                           (Sig : LogOSSignature ℓ)
                           (Q   : QAdapter ℓ)
                           : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  field
    LCUA : LCUObsAssumptions Sig Q

    -- Locality/causality as abstract constraints (kept opaque here).
    Locality  : Set ℓ
    Causality : Set ℓ

    -- A per-program count of classicalization/measurement events.
    meas : Cosp → ℕ

    -- Classical information extracted by a program (in bits, say).
    info : Cosp → ℕ

    -- Capacity bound: each measurement event yields at most κ bits.
    κ : ℕ
    info≤κ·meas : ∀ f → info f ≤ℕ mul κ (meas f)

    -- Reversibility compatibility: local-unitary programs need no measurements.
    unitary→meas0 : ∀ f → LCUObsAssumptions.LocalUnitary LCUA f → meas f ≡ 0
