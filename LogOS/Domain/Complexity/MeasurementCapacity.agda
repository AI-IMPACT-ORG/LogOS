{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.MeasurementCapacity where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; suc)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ; ≤ℕ-refl; weakenRight) public

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.Domain.Complexity.LCUToLandauer as LCU
open import LogOS.Domain.Complexity.HartleyEntropy using (H₀)
import Data.NatLog2 as NatLog2

open NatLog2 public using (plusR; mul)
open NatLog2 using (exp₂; log₂-mono; log₂-exp₂; plusR-monoL; plusR-monoR; mul-monoR)

-- A LogOS-native “measurement capacity” pack:
-- it bounds how much *classical information* can be extracted (classicalized)
-- per local event, under locality/causality constraints.
--
-- This stays compatible with reversible computation:
-- unitary/reversible dynamics can run arbitrarily long; only classicalization is charged.

-- “Extractable classical info” is abstracted as a natural number.
-- Models can instantiate this with (log of) distinguishable outcomes, mutual information, etc.
-- For a fully internal, computable notion of “log in bits” on ℕ, see `Data.NatLog2.log₂`.

-- Monotonicity of addition and multiplication w.r.t. ≤ℕ (needed for time/throughput bridges).

monoPlusL : ∀ {a b} → a ≤ℕ b → ∀ c → plusR a c ≤ℕ plusR b c
monoPlusL = plusR-monoL

lePlusR : ∀ a c → a ≤ℕ plusR a c
lePlusR = NatLog2.lePlusR

monoPlusR : ∀ {c d} → c ≤ℕ d → ∀ a → plusR a c ≤ℕ plusR a d
monoPlusR = plusR-monoR

monoMul : ∀ k {a b} → a ≤ℕ b → mul k a ≤ℕ mul k b
monoMul = mul-monoR

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

-- Turn an “outcome count fits under 2^(budget)” bound into a `MeasurementCapacity`
-- whose `info` is literally Hartley entropy `H₀` of the outcome count.
--
-- This is a defensible bridge:
--   outcomes(f) ≤ 2^(κ·meas(f))  ⇒  log₂(outcomes(f)) ≤ κ·meas(f)
--
-- No probabilistic/shannonian structure is assumed: everything is over ℕ.

fromOutcomeBound
  : ∀ {ℓ : Level}
    (Sig : LogOSSignature ℓ)
    (Q   : QAdapter ℓ)
    (LCUA : LCU.LCUObsAssumptions Sig Q)
  → (Locality  : Set ℓ)
  → (Causality : Set ℓ)
  → (meas      : LogOSSignature.Cosp Sig → ℕ)
  → (outcomes  : LogOSSignature.Cosp Sig → ℕ)
  → (κ         : ℕ)
  → (outcomes≤2^κ·meas : ∀ f → outcomes f ≤ℕ exp₂ (mul κ (meas f)))
  → (unitary→meas0 : ∀ f → LCU.LCUObsAssumptions.LocalUnitary LCUA f → meas f ≡ 0)
  → MeasurementCapacity Sig Q
fromOutcomeBound {ℓ} Sig Q LCUA Locality Causality meas outcomes κ outcomes≤2^κ·meas unitary→meas0 =
  record
    { LCUA = LCUA
    ; Locality = Locality
    ; Causality = Causality
    ; meas = meas
    ; info = λ f → H₀ (outcomes f)
    ; κ = κ
    ; info≤κ·meas = λ f →
        trans≤ℕ
          (log₂-mono (outcomes≤2^κ·meas f))
          (subst
            (λ x → H₀ (exp₂ (mul κ (meas f))) ≤ℕ x)
            (log₂-exp₂ (mul κ (meas f)))
            ≤ℕ-refl)
    ; unitary→meas0 = unitary→meas0
    }
