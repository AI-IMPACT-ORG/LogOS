{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Fuel where

-- Primitive fuel/index profile shared by resource and iteration patterns.
-- This keeps "step-indexed recursion over fuel" abstract while preserving a
-- concrete default by inheriting from `ℕ` through `LogOS.Prelude`.

open import LogOS.Prelude as Prelude
open import LogOS.Host.Nat renaming (zero to zeroℕ; suc to sucℕ)

-- Universe note: `iter` is polymorphic in `A`, so the profile lives in `Setω`.
record FuelProfile : Setω where
  field
    Fuel : Set
    zero : Fuel
    suc  : Fuel → Fuel
    iter : ∀ {ℓ} {A : Set ℓ} → (A → A) → Fuel → A → A
    -- S-tier computation laws for the chosen iterator.
    iter-zero : ∀ {ℓ} {A : Set ℓ} (f : A → A) (a : A) → iter f zero a ≡ a
    iter-succ : ∀ {ℓ} {A : Set ℓ} (f : A → A) (n : Fuel) (a : A) → iter f (suc n) a ≡ iter f n (f a)

open FuelProfile public using (Fuel; zero; suc; iter; iter-zero; iter-succ)

NatFuel : FuelProfile
NatFuel =
  record
    { Fuel = ℕ
    ; zero = zeroℕ
    ; suc = sucℕ
    ; iter = iterℕ
    ; iter-zero = iterℕ-zero
    ; iter-succ = iterℕ-succ
    }
  where
    iterℕ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → A → A
    iterℕ f zeroℕ a = a
    iterℕ f (sucℕ n) a = iterℕ f n (f a)

    iterℕ-zero : ∀ {ℓ} {A : Set ℓ} (f : A → A) (a : A) → iterℕ f zeroℕ a ≡ a
    iterℕ-zero f a = refl

    iterℕ-succ : ∀ {ℓ} {A : Set ℓ} (f : A → A) (n : ℕ) (a : A) → iterℕ f (sucℕ n) a ≡ iterℕ f n (f a)
    iterℕ-succ f n a = refl
