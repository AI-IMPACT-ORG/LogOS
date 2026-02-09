{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.Reduction where

-- Standard many-one reductions, with optional polynomial size bounds.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ↔-sym; ¬_)

open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; trans≤ℕ)
open import LogOS.Prelude using (Σ; _,_; _×_)

open import LogOS.Complexity.Poly using (PolyPred)
open import LogOS.Complexity.LanguageWitness using (DeciderI; reindexDeciderI)
open import LogOS.Computation.Decider using (mapDecider)
import LogOS.Complexity.PvsNPLedger as CP

record ManyOneReduction
  {ℓI₁ ℓI₂ ℓP ℓQ : Level}
  (Input₁ : Set ℓI₁)
  (Input₂ : Set ℓI₂)
  (P : Input₁ → Set ℓP)
  (Q : Input₂ → Set ℓQ)
  : Set (lsuc (ℓI₁ ⊔ ℓI₂ ⊔ ℓP ⊔ ℓQ)) where
  field
    map   : Input₁ → Input₂
    sound : ∀ x → P x → Q (map x)
    complete : ∀ x → Q (map x) → P x

  correctness : ∀ x → P x ↔ Q (map x)
  correctness x = intro (sound x) (complete x)

-- Decider transport along a reduction.
deciderFromReduction
  : ∀ {ℓI₁ ℓI₂ ℓPQ}
    {Input₁ : Set ℓI₁} {Input₂ : Set ℓI₂}
    {P : Input₁ → Set ℓPQ} {Q : Input₂ → Set ℓPQ}
  → ManyOneReduction Input₁ Input₂ P Q
  → DeciderI Input₂ Q
  → DeciderI Input₁ P
deciderFromReduction R D =
  mapDecider (λ x → ↔-sym (ManyOneReduction.correctness R x))
    (reindexDeciderI (ManyOneReduction.map R) _ D)

record PolyReduction
  {ℓI₁ ℓI₂ ℓP ℓQ : Level}
  (Input₁ : Set ℓI₁)
  (Input₂ : Set ℓI₂)
  (P : Input₁ → Set ℓP)
  (Q : Input₂ → Set ℓQ)
  (size₁ : Input₁ → ℕ)
  (size₂ : Input₂ → ℕ)
  (poly : PolyPred)
  : Set (lsuc (ℓI₁ ⊔ ℓI₂ ⊔ ℓP ⊔ ℓQ)) where
  open PolyPred poly
  field
    red       : ManyOneReduction Input₁ Input₂ P Q
    bound     : ℕ → ℕ
    polyBound : isPoly bound
    sizeBound : ∀ x → size₂ (ManyOneReduction.map red x) ≤ℕ bound (size₁ x)

deciderFromPolyReduction
  : ∀ {ℓI₁ ℓI₂ ℓPQ}
    {Input₁ : Set ℓI₁} {Input₂ : Set ℓI₂}
    {P : Input₁ → Set ℓPQ} {Q : Input₂ → Set ℓPQ}
    {size₁ : Input₁ → ℕ} {size₂ : Input₂ → ℕ}
    {poly : PolyPred}
  → PolyReduction Input₁ Input₂ P Q size₁ size₂ poly
  → DeciderI Input₂ Q
  → DeciderI Input₁ P
deciderFromPolyReduction R =
  deciderFromReduction (PolyReduction.red R)

module Classical
  {ℓI₁ ℓI₂ ℓ : Level}
  (Input₁ : Set ℓI₁)
  (Input₂ : Set ℓI₂)
  (size₁ : Input₁ → ℕ)
  (size₂ : Input₂ → ℕ)
  (Pℕ : PolyPred)
  where

  module C₁ = CP.For {ℓI = ℓI₁} {ℓW = ℓ} {ℓ = ℓ} Input₁ size₁ Pℕ
  module C₂ = CP.For {ℓI = ℓI₂} {ℓW = ℓ} {ℓ = ℓ} Input₂ size₂ Pℕ
  open PolyPred Pℕ

  inPFromPolyReduction
    : ∀ {P Q}
      (R : PolyReduction Input₁ Input₂ P Q size₁ size₂ Pℕ)
      (inQ : C₂.InP Q)
      (boundMono : ∀ {m n} → m ≤ℕ n →
                     C₂.PolyTimeDecider.bound (proj₁ inQ) m ≤ℕ
                     C₂.PolyTimeDecider.bound (proj₁ inQ) n)
      (polyComp : isPoly (λ n →
        C₂.PolyTimeDecider.bound (proj₁ inQ) (PolyReduction.bound R n)))
      → C₁.InP P
  inPFromPolyReduction R (pd , _) boundMono polyComp =
    ( record
        { D = deciderFromReduction (PolyReduction.red R) (C₂.PolyTimeDecider.D pd)
        ; cost = λ x → C₂.PolyTimeDecider.cost pd
                           (ManyOneReduction.map (PolyReduction.red R) x)
        ; bound = λ n → C₂.PolyTimeDecider.bound pd (PolyReduction.bound R n)
        ; polyBound = polyComp
        ; cost≤ = λ x →
            let mapx = ManyOneReduction.map (PolyReduction.red R) x in
            let c≤ = C₂.PolyTimeDecider.cost≤ pd mapx in
            let sz≤ = PolyReduction.sizeBound R x in
            let b≤ = boundMono sz≤ in
            trans≤ℕ c≤ b≤
        }
    , tt
    )

  notInPFromPolyReduction
    : ∀ {P Q}
      (R : PolyReduction Input₁ Input₂ P Q size₁ size₂ Pℕ)
      (boundMono : ∀ (pd : C₂.PolyTimeDecider Q) {m n} → m ≤ℕ n →
                     C₂.PolyTimeDecider.bound pd m ≤ℕ
                     C₂.PolyTimeDecider.bound pd n)
      (polyComp : ∀ (pd : C₂.PolyTimeDecider Q) →
        isPoly (λ n → C₂.PolyTimeDecider.bound pd (PolyReduction.bound R n)))
      → ¬ C₁.InP P
      → ¬ C₂.InP Q
  notInPFromPolyReduction R boundMono polyComp notP inQ =
    notP (inPFromPolyReduction R inQ (boundMono (proj₁ inQ)) (polyComp (proj₁ inQ)))
