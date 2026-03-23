{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.EngineeringDimension where

-- Engineering dimension / “power counting”, refinement-first.
--
-- This is the minimal, reusable fragment behind dimensional-analysis-style
-- reasoning:
--
-- 1. choose a finite-join prequantale boundary (finite joins + multiplication, laws in `≈`),
-- 2. interpret objects of interest by an observation map `obs : A → Con CP`,
-- 3. say a transformation `f` has grade `g` when:
--      obs (f x) ⊑ obs x · g
-- 4. derive iteration bounds by multiplying grades.
--
-- This generalises the `QAdapter`-specialised budget transport:
-- a `QAdapter` induces a finite-join prequantale on its scale boundary
-- (`ScaleJoinPrequantale`), and any `BudgetPort` supplies an observation map
-- via `μ`.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.ConPreorder using
  ( ConPreorder; Con; _⊑_; refl⊑; _≈_
  )
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Iteration using (iter)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)

-- n-fold grade multiplication (right-associated).
pow
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (JP : JoinPrequantale CP)
  → Con CP → ℕ → Con CP
pow {CP = CP} JP g zero =
  let open JoinPrequantale JP in
  e
pow {CP = CP} JP g (suc n) =
  let open JoinPrequantale JP in
  g · pow JP g n

record GradedTransport
  {ℓA ℓB ℓCon ℓRel : Level}
  {A : Set ℓA}
  {B : Set ℓB}
  {CP : ConPreorder ℓCon ℓRel}
  (JP : JoinPrequantale CP)
  (obsA : A → Con CP)
  (obsB : B → Con CP)
  (f : A → B)
  : Set (lsuc (ℓA ⊔ ℓB ⊔ ℓCon ⊔ ℓRel)) where
  open JoinPrequantale JP
  field
    grade : Con CP

    -- Core inequality (“engineering dimension bound”):
    -- the interpreted output is bounded by the interpreted input times the grade.
    graded : ∀ x → _⊑_ CP (obsB (f x)) (obsA x · grade)

open GradedTransport public
idGradedTransport
  : ∀ {ℓA ℓCon ℓRel : Level}
    {A : Set ℓA}
    {CP : ConPreorder ℓCon ℓRel}
  → (JP : JoinPrequantale CP)
  → (obs : A → Con CP)
  → GradedTransport JP obs obs (λ x → x)
idGradedTransport {CP = CP} JP obs =
  let open JoinPrequantale JP in
  record
    { grade = e
    ; graded = λ x → snd (·-idr≈ (obs x))
    }

composeGradedTransport
  : ∀ {ℓA ℓB ℓC ℓCon ℓRel : Level}
    {A : Set ℓA}
    {B : Set ℓB}
    {C : Set ℓC}
    {CP : ConPreorder ℓCon ℓRel}
  → (JP : JoinPrequantale CP)
  → {obs₁ : A → Con CP}
  → {obs₂ : B → Con CP}
  → {obs₃ : C → Con CP}
  → {f : A → B}
  → {g : B → C}
  → GradedTransport JP obs₁ obs₂ f
  → GradedTransport JP obs₂ obs₃ g
  → GradedTransport JP obs₁ obs₃ (λ x → g (f x))
composeGradedTransport
  {CP = CP} JP
  {obs₁ = obs₁} {obs₂ = obs₂} {obs₃ = obs₃}
  {f = f} {g = g} tf tg =
  let open JoinPrequantale JP in
  let open ≤-Reasoning CP using (begin⊑_; _⊑⟨_⟩_; _∎⊑) in
  record
    { grade = grade tf · grade tg
    ; graded =
        λ x →
          let
            step₁ : _⊑_ CP (obs₃ (g (f x))) (obs₂ (f x) · grade tg)
            step₁ = graded tg (f x)

            step₂ : _⊑_ CP (obs₂ (f x) · grade tg) ((obs₁ x · grade tf) · grade tg)
            step₂ = ·-mono (graded tf x) (refl⊑ CP)

            step₃ : _⊑_ CP ((obs₁ x · grade tf) · grade tg) (obs₁ x · (grade tf · grade tg))
            step₃ = fst (·-assoc≈ (obs₁ x) (grade tf) (grade tg))
          in
          begin⊑_
            ( obs₃ (g (f x)) ⊑⟨ step₁ ⟩
              obs₂ (f x) · grade tg ⊑⟨ step₂ ⟩
              (obs₁ x · grade tf) · grade tg ⊑⟨ step₃ ⟩
              obs₁ x · (grade tf · grade tg) ∎⊑
            )
    }

-- Iteration bound (“power counting”):
-- if one step grows dimension by grade `g`, then n steps grow it by `g^n`.
iterBound
  : ∀ {ℓA ℓCon ℓRel : Level}
    {A : Set ℓA}
    {CP : ConPreorder ℓCon ℓRel}
  → (JP : JoinPrequantale CP)
  → {obs : A → Con CP}
  → {f : A → A}
  → (Tf : GradedTransport JP obs obs f)
  → (n : ℕ)
  → (x : A)
  → _⊑_ CP (obs (iter f n x))
      (JoinPrequantale._·_ JP (obs x) (pow JP (grade Tf) n))
iterBound {CP = CP} JP {obs = obs} {f = f} Tf zero x =
  let open JoinPrequantale JP in
  -- iter f 0 x = x, and pow g 0 = e.
  snd (·-idr≈ (obs x))
iterBound {CP = CP} JP {obs = obs} {f = f} Tf (suc n) x =
  let
    open JoinPrequantale JP
    ih
      : _⊑_ CP
          (obs (iter f n (f x)))
          (obs (f x) · pow JP (grade Tf) n)
    ih = iterBound JP Tf n (f x)

    step
      : _⊑_ CP
          (obs (f x))
          (obs x · grade Tf)
    step = graded Tf x

    mul
      : _⊑_ CP
          (obs (f x) · pow JP (grade Tf) n)
          ((obs x · grade Tf) · pow JP (grade Tf) n)
    mul = ·-mono step (refl⊑ CP)

    assoc
      : _⊑_ CP
          ((obs x · grade Tf) · pow JP (grade Tf) n)
          (obs x · (grade Tf · pow JP (grade Tf) n))
    assoc = fst (·-assoc≈ (obs x) (grade Tf) (pow JP (grade Tf) n))

  in
  let open ≤-Reasoning CP using (begin⊑_; _⊑⟨_⟩_; _∎⊑) in
  begin⊑_
    ( obs (iter f n (f x)) ⊑⟨ ih ⟩
      obs (f x) · pow JP (grade Tf) n ⊑⟨ mul ⟩
      (obs x · grade Tf) · pow JP (grade Tf) n ⊑⟨ assoc ⟩
      obs x · (grade Tf · pow JP (grade Tf) n) ∎⊑
    )
