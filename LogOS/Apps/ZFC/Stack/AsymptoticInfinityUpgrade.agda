{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticInfinityUpgrade where

-- Infinity (ω) from the fixed-point spine, but expressed in the same
-- “asymptotic reification” style as `Stack.AsymptoticReification`.
--
-- Summary (epistemically strict):
--
-- - We assume a reification port on the membership-local predicate boundary
--   (membership of `reify P` matches `Flow P`).
-- - We assume stability only for the specific predicates needed to build the
--   successor-closure endomorphism `step`.
-- - We assume σ-directed completeness (`SigmaDCPO`) plus σ-co-continuity of
--   `step` to obtain ω as a greatest fixed point (ν) in the reverse-inclusion
--   set boundary.
--
-- This is an explicit assumption boundary (a metalogical route to Infinity),
-- not a derivation of Infinity from the other ZF axioms.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.Flow using (Flow)
open import LogOS.LT.ConPreorder using (Opp; _⊑_)
open import LogOS.LT.Sup.FinSup using (HasTop)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO)
open import LogOS.LT.View using (μ)
import LogOS.LT.Sup.AbstractCoKleene as CoKleene

import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR

module For {ℓ : Level} (C : ZF.SetContext {ℓ}) (R : AR.PredicateReification C) where
  open ZF.SetContext C
  open AR.PredicateReification R
  module Core = AR.Core C R
  open Core
  module D = ZF.DerivedCore coreSigᵣ

  -- ------------------------------------------------------------------------
  -- The successor-closure endomorphism `step`.
  --
  -- We use the “core-only” derived 0 and succ; ω is a fixed point of:
  --
  --   step X = {0} ∪ succ[X]
  --
  -- where succ[X] is presented as a reified membership predicate.

  zeroSet : SetU
  zeroSet = μ D.ZeroV tt

  singletonSet : SetU → SetU
  singletonSet x = μ PairVᵣ (x , x)

  union₂Set : SetU → SetU → SetU
  union₂Set x y = μ UnionVᵣ (μ PairVᵣ (x , y))

  succSet : SetU → SetU
  succSet x = union₂Set x (singletonSet x)

  SuccImagePred : SetU → Predicate
  SuccImagePred X z = Σ SetU (λ u → u ∈ X × (z ≈ succSet u))

  succImage : (X : SetU) → Reifiable (SuccImagePred X) → SetU
  succImage X rX = reify (SuccImagePred X) rX

  step : (r : ∀ X → Reifiable (SuccImagePred X)) → SetU → SetU
  step r X = union₂Set (singletonSet zeroSet) (succImage X (r X))

  -- ------------------------------------------------------------------------
  -- Assumptions: stability + completeness.

  record CoKleeneInfinityAssumptionsᵣ : Set (lsuc (lsuc ℓ)) where
    field
      coreStability : CoreStability

      -- Admissibility for the specific “successor image” predicates used by `step`.
      succImageReifiable
        : ∀ X → Reifiable (SuccImagePred X)

      -- Stability for the specific “successor image” predicates used by `step`.
      succImageStable
        : ∀ X → _⊑_ PredBnd (Flow GC (SuccImagePred X)) (SuccImagePred X)

      -- Completeness/continuity assumptions for the ν construction.
      SDᵒᵖ : SigmaDCPO (Opp SetBnd)
      stepCoCont : CoKleene.SigmaCoContinuous SetBnd SDᵒᵖ (step succImageReifiable)

  -- Empty set is top in the reverse-inclusion boundary order.
  topSetBnd : HasTop SetBnd
  topSetBnd =
    record
      { ⊤ᵇ = zeroSet
      ; ⊤ᵇ-greatest =
          λ _ z z∈0 → ⊥-elim (empty-specᵣ z z∈0)
      }

  module AsymptoticInfinityUpgradeLocal (A : CoKleeneInfinityAssumptionsᵣ) where
    open CoKleeneInfinityAssumptionsᵣ A

    stepA : SetU → SetU
    stepA = step succImageReifiable

    succImageA : SetU → SetU
    succImageA X = succImage X (succImageReifiable X)

    module CK = CoKleene.CoKleeneLocal topSetBnd SDᵒᵖ stepA stepCoCont

    ω : SetU
    ω = CK.ν

    omegaSig : ZF.ZFSignatureOmega C
    omegaSig = record { OmegaV = record { μ = λ _ → ω } }

    private
      -- Core laws for the reified constructors (needed for membership reasoning).
      coreLaws : ZF.ZFLawsCore C coreSigᵣ
      coreLaws = coreLawsᵣ coreStability

      open ZF.ZFLawsCore coreLaws using (empty-spec; pairing-spec; union-spec)

      mem-singleton↔ : ∀ {x z} → (z ∈ singletonSet x) ↔ (z ≈ x)
      mem-singleton↔ {x} {z} =
        let p = pairing-spec x x z in
        intro
          (λ z∈ →
            let e = _↔_.to p z∈ in
            elim e)
          (λ zx → _↔_.from p (inj₁ zx))
        where
          elim : ∀ {A : Set ℓ} → (A ⊎ A) → A
          elim (inj₁ a) = a
          elim (inj₂ a) = a

      mem-succImage↔
        : ∀ X z
        → (z ∈ succImageA X) ↔ SuccImagePred X z
      mem-succImage↔ X z =
        AR.mem-reify-stable↔
          R
          (SuccImagePred X)
          (succImageReifiable X)
          (succImageStable X)
          z

      mem-step↔
        : ∀ (X z : SetU)
        → (z ∈ stepA X)
            ↔ ( (z ≈ zeroSet)
              ⊎ (Σ SetU (λ y → y ∈ X × (z ≈ succSet y))) )
      mem-step↔ X z =
        intro (to z) (from z)
        where
          to
            : ∀ z
            → z ∈ stepA X
            → (z ≈ zeroSet)
                ⊎ (Σ SetU (λ y → y ∈ X × (z ≈ succSet y)))
          to z z∈ with _↔_.to (union-spec (μ PairVᵣ (singletonSet zeroSet , succImageA X)) z) z∈
          ... | (y , (y∈pair , z∈y)) with _↔_.to (pairing-spec (singletonSet zeroSet) (succImageA X) y) y∈pair
          ... | inj₁ y≈0 =
            inj₁ (_↔_.to mem-singleton↔ (fst y≈0 z z∈y))
          ... | inj₂ y≈img with _↔_.to (mem-succImage↔ X z) (fst y≈img z z∈y)
          ... | (u , (u∈X , z≈su)) =
            inj₂ (u , (u∈X , z≈su))

          from
            : ∀ z
            → ( (z ≈ zeroSet)
                ⊎ (Σ SetU (λ y → y ∈ X × (z ≈ succSet y))) )
            → z ∈ stepA X
          from z (inj₁ z≈0) =
            _↔_.from (union-spec (μ PairVᵣ (singletonSet zeroSet , succImageA X)) z)
              ( singletonSet zeroSet
              , ( _↔_.from (pairing-spec (singletonSet zeroSet) (succImageA X) (singletonSet zeroSet))
                    (inj₁ (refl≈ (singletonSet zeroSet)))
                , _↔_.from mem-singleton↔ z≈0
                )
              )
          from z (inj₂ (u , (u∈X , z≈su))) =
            _↔_.from (union-spec (μ PairVᵣ (singletonSet zeroSet , succImageA X)) z)
              ( succImageA X
              , ( _↔_.from (pairing-spec (singletonSet zeroSet) (succImageA X) (succImageA X))
                    (inj₂ (refl≈ (succImageA X)))
                , _↔_.from (mem-succImage↔ X z) (u , (u∈X , z≈su))
                )
              )

      infinity-spec
        : ∀ z
        → (z ∈ ω)
            ↔ ( (z ≈ μ D.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ μ D.SuccV y))) )
      infinity-spec z =
        intro to from
        where
          -- Fixed point property from CoKleene, rewritten as extensional equality.
          fix : (stepA ω) ≈ ω
          fix = snd CK.fν≈ν , fst CK.fν≈ν

          to
            : z ∈ ω
            → ( (z ≈ μ D.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ μ D.SuccV y))) )
          to z∈ω =
            _↔_.to (mem-step↔ ω z) (snd fix z z∈ω)

          from
            : ( (z ≈ μ D.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ μ D.SuccV y))) )
            → z ∈ ω
          from disj =
            fst fix z (_↔_.from (mem-step↔ ω z) disj)

    infinityLaws : ZF.ZFLawsInfinity C coreSigᵣ omegaSig
    infinityLaws =
      record
        { infinity-spec = infinity-spec }

  -- Convenience re-exports: treat the inner module as an explicit upgrade step.
  omegaSig : CoKleeneInfinityAssumptionsᵣ → ZF.ZFSignatureOmega C
  omegaSig A =
    let module U = AsymptoticInfinityUpgradeLocal A in
    U.omegaSig

  infinityLaws
    : (A : CoKleeneInfinityAssumptionsᵣ)
    → ZF.ZFLawsInfinity C coreSigᵣ (omegaSig A)
  infinityLaws A =
    let module U = AsymptoticInfinityUpgradeLocal A in
    U.infinityLaws
