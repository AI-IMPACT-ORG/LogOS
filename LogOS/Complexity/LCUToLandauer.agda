{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.LCUToLandauer where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥)

open import LogOS.Prelude using (Σ; _,_; _×_; fst; snd)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)
import LogOS.Theorems.Meta.Landauer as L

-- A “locality/causality/local unitarity” axiom pack with enough structure to
-- *derive* a Landauer-style lower bound for irreversible (“merging”) programs.
--
-- The idea is intentionally modest and LogOS-native:
-- - we do not commit to a Hilbert space;
-- - “unitarity” is reflected only through injectivity on an observable carrier;
-- - “merging” is defined as non-injectivity on observables; and
-- - Landauer is obtained from an axiom that any non-unitary step costs ≥ L.

Injective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → Set (ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

record LCUObsAssumptions {ℓ : Level}
                         (Sig : LogOSSignature ℓ)
                         (Q   : QAdapter ℓ)
                         : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  open QAdapter Q renaming (Scale to S; _≤s_ to _≤E_)
  field
    -- The three “physical computation” pillars, kept abstract (models choose formalizations).
    Locality     : Set ℓ
    Causality    : Set ℓ

    -- Observables and program action on observables.
    Obs : Set ℓ
    act : Cosp → Obs → Obs

    -- Local unitarity exposed as injectivity on observables.
    LocalUnitary : Cosp → Set ℓ
    unitary-inj  : ∀ f → LocalUnitary f → Injective (act f)

    -- Energy/cost semantics (from the adapter’s Scale carrier).
    L    : S
    cost : Cosp → S

    -- Core physical “dissipation axiom”: any observable-level non-unitary action costs ≥ L.
    nonUnitary-ref : SatRefinement₀ Cosp
                      (λ _ f → ¬ LocalUnitary f)
                      (λ _ f → _≤E_ L (cost f))

  nonUnitary→lower : ∀ f → ¬ LocalUnitary f → _≤E_ L (cost f)
  nonUnitary→lower f nu = sat-→₀ nonUnitary-ref f nu

-- Irreversible merge at the observable level: two distinct observations become equal.

Merges
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : LCUObsAssumptions Sig Q)
  → LogOSSignature.Cosp Sig → Set ℓ
Merges {Sig = Sig} A f =
  Σ (LCUObsAssumptions.Obs A) (λ x →
    Σ (LCUObsAssumptions.Obs A) (λ y →
      (¬ (x ≡ y)) × (LCUObsAssumptions.act A f x ≡ LCUObsAssumptions.act A f y)))

merge→¬unitary
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : LCUObsAssumptions Sig Q)
    (f : LogOSSignature.Cosp Sig)
  → Merges A f
  → ¬ (LCUObsAssumptions.LocalUnitary A f)
merge→¬unitary A f (x , (y , (x≠y , eq))) u =
  x≠y (LCUObsAssumptions.unitary-inj A f u eq)

-- Derived Landauer pack.

toLandauer
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : LCUObsAssumptions Sig Q)
  → L.LandauerAssumptions Sig Q
toLandauer {Sig = Sig} {Q = Q} A =
  record
    { L = LCUObsAssumptions.L A
    ; cost = LCUObsAssumptions.cost A
    ; Merges = Merges A
    ; merge-ref =
        record
          { sat-→ = λ _ f m →
              LCUObsAssumptions.nonUnitary→lower A f (merge→¬unitary A f m)
          }
    }
