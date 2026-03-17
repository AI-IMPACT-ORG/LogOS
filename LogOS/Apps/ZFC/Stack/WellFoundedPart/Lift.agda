{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.WellFoundedPart.Lift where

-- Lift a base ZF stack to its “well-founded part” by restricting the universe to
-- `Acc _∈_` objects and transporting the constructor laws across projections.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Stack.WellFoundedPart.Universe as Universe
import LogOS.Apps.ZFC.Stack.WellFoundedPart.Closure as Closure

module ForBase {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) where
  open Tower.ZFStackBase B
  module U = Universe.ForBase B
  open U

  module C = Closure.ForBase B
  open C using (BaseWFClosure; wfOmega; wf-empty; wf-pair; wf-union; wf-powerset)

  baseᵂ : BaseWFClosure → Tower.ZFStackBase {ℓ}
  baseᵂ C =
    record
      { ctx = ctxᵂ
      ; coreSig = coreSigᵂ
      ; powSig = powSigᵂ
      ; omegaSig = omegaSigᵂ
      ; coreLaws = coreLawsᵂ
      ; powersetLaws = powersetLawsᵂ
      ; infinityLaws = infinityLawsᵂ
      }
      where
      open BaseWFClosure C
      infix 4 _⊆ᵂ_ _≈ᵂ_
      _⊆ᵂ_ : SetUᵂ → SetUᵂ → Set ℓ
      _⊆ᵂ_ x y = ∀ z → z ∈ᵂ x → z ∈ᵂ y

      _≈ᵂ_ : SetUᵂ → SetUᵂ → Set ℓ
      _≈ᵂ_ x y = (x ⊆ᵂ y) × (y ⊆ᵂ x)

      -- Lift/downgrade extensional equality across the accessibility wrapper.
      lift-≈ : ∀ {x y : SetUᵂ}
        → (⌞ x ⌟ ≈ ⌞ y ⌟)
        → (x ≈ᵂ y)
      lift-≈ {x} {y} h =
        ( (λ z z∈x → fst h ⌞ z ⌟ z∈x)
        , (λ z z∈y → snd h ⌞ z ⌟ z∈y)
        )

      strip-≈ : ∀ {x y : SetUᵂ}
        → (x ≈ᵂ y)
        → (⌞ x ⌟ ≈ ⌞ y ⌟)
      strip-≈ {x = (x₀ , wx)} {y = (y₀ , wy)} h =
        ( (λ z z∈x → fst h (z , wf-member wx z∈x) z∈x)
        , (λ z z∈y → snd h (z , wf-member wy z∈y) z∈y)
        )

      liftPairSum : ∀ (a b c : SetUᵂ)
        → (⌞ a ⌟ ≈ ⌞ b ⌟) ⊎ (⌞ a ⌟ ≈ ⌞ c ⌟)
        → ((a ≈ᵂ b) ⊎ (a ≈ᵂ c))
      liftPairSum a b c (inj₁ hab) = inj₁ (lift-≈ {x = a} {y = b} hab)
      liftPairSum a b c (inj₂ hac) = inj₂ (lift-≈ {x = a} {y = c} hac)

      stripPairSum : ∀ (a b c : SetUᵂ)
        → ((a ≈ᵂ b) ⊎ (a ≈ᵂ c))
        → (⌞ a ⌟ ≈ ⌞ b ⌟) ⊎ (⌞ a ⌟ ≈ ⌞ c ⌟)
      stripPairSum a b c (inj₁ hab) = inj₁ (strip-≈ {x = a} {y = b} hab)
      stripPairSum a b c (inj₂ hac) = inj₂ (strip-≈ {x = a} {y = c} hac)

      base-pairing-spec = Tower.ZFStackBase.pairing-spec B
      base-union-spec = Tower.ZFStackBase.union-spec B
      base-powerset-spec = Tower.ZFStackBase.powerset-spec B
      base-infinity-spec = Tower.ZFStackBase.infinity-spec B

      -- Lifted constructor views (pack the underlying set with its `Acc` proof).
      coreSigᵂ : ZF.ZFSignatureCore ctxᵂ
      coreSigᵂ =
        record
              { EmptyV =
              record { μ = λ _ → emptySet , wf-empty }
          ; PairV =
              record
                { μ =
                    λ (x , y) →
                      pairSet ⌞ x ⌟ ⌞ y ⌟
                      , wf-pair (wf x) (wf y)
                }
          ; UnionV =
              record
                { μ =
                    λ x →
                      unionSet ⌞ x ⌟
                      , wf-union (wf x)
                }
          }

      powSigᵂ : ZF.ZFSignaturePowerset ctxᵂ
      powSigᵂ =
        record
          { PowersetV =
              record
                { μ =
                    λ x →
                      powersetSet ⌞ x ⌟
                      , wf-powerset (wf x)
                }
          }

      omegaSigᵂ : ZF.ZFSignatureOmega ctxᵂ
      omegaSigᵂ =
        record { OmegaV = record { μ = λ _ → omegaSet , BaseWFClosure.wfOmega C } }

      -- Laws: reuse the original laws, transporting along projections.
      --
      -- For sets in the restricted universe, membership is unchanged
      -- definitionally (it forgets `Acc` proofs), so the existing specs
      -- lift directly.
      coreLawsᵂ : ZF.ZFLawsCore ctxᵂ coreSigᵂ
      coreLawsᵂ =
        record
          { empty-spec =
              λ (z , _) z∈e → empty-spec z z∈e
          ; pairing-spec =
              λ (x : SetUᵂ) (y : SetUᵂ) (z : SetUᵂ) →
                intro
                  (λ hz →
                    liftPairSum z x y
                      (_↔_.to (base-pairing-spec ⌞ x ⌟ ⌞ y ⌟ ⌞ z ⌟) hz))
                  (λ hz →
                    _↔_.from (base-pairing-spec ⌞ x ⌟ ⌞ y ⌟ ⌞ z ⌟)
                      (stripPairSum z x y hz)
                  )
          ; union-spec =
              λ x z →
                let
                  (x₀ , wx) = x
                  (z₀ , _) = z
                in
                intro
                  (λ z∈U →
                    let
                      (y , (y∈x , z∈y)) =
                        _↔_.to (base-union-spec x₀ z₀) z∈U
                    in
                    ( (y , wf-member wx y∈x)
                    , ( y∈x
                      , z∈y
                      )
                    )
                  )
                  (λ (y , (y∈x , z∈y)) →
                    _↔_.from (base-union-spec x₀ z₀)
                      ( ⌞ y ⌟
                      , (y∈x , z∈y)
                      )
                  )
          }

      powersetLawsᵂ : ZF.ZFLawsPowerset ctxᵂ powSigᵂ
      powersetLawsᵂ =
        record
              { powerset-spec =
                  λ x z →
                    let
                      (x₀ , wx) = x
                      (z₀ , wz) = z
                    in
                    intro
                      (λ z∈P →
                    let inX = _↔_.to (base-powerset-spec x₀ z₀) z∈P in
                    λ w w∈z → inX (⌞ w ⌟) w∈z
                      )
                      (λ hz →
                    _↔_.from (base-powerset-spec x₀ z₀)
                      (λ w w∈z → hz (w , wf-member wz w∈z) w∈z)
                      )
              }

      infinityLawsᵂ : ZF.ZFLawsInfinity ctxᵂ coreSigᵂ omegaSigᵂ
      infinityLawsᵂ =
        record
          { infinity-spec =
              λ z →
                intro
                  (to∞ z)
                  (from∞ z)
          }
          where
            omegaVᵂ : SetUᵂ
            omegaVᵂ = μ (ZF.ZFSignatureOmega.OmegaV omegaSigᵂ) tt

            zeroVᵂ : SetUᵂ
            zeroVᵂ = μ (ZF.DerivedCore.ZeroV coreSigᵂ) tt

            succVᵂ : SetUᵂ → SetUᵂ
            succVᵂ = μ (ZF.DerivedCore.SuccV coreSigᵂ)

            to∞ : ∀ z → z ∈ᵂ omegaVᵂ → (z ≈ᵂ zeroVᵂ) ⊎ (Σ SetUᵂ (λ y → y ∈ᵂ omegaVᵂ × (z ≈ᵂ succVᵂ y)))
            to∞ z z∈ω with _↔_.to (base-infinity-spec (⌞ z ⌟)) z∈ω
            ... | inj₁ z≈z0 = inj₁ (lift-≈ {x = z} {y = zeroVᵂ} z≈z0)
            ... | inj₂ (y , (y∈ωx , z≈sy)) =
              let
                yᵂ : SetUᵂ
                yᵂ = (y , wf-member (BaseWFClosure.wfOmega C) y∈ωx)
                zy≈sy : z ≈ᵂ succVᵂ yᵂ
                zy≈sy = lift-≈ {x = z} {y = succVᵂ yᵂ} z≈sy
              in
              inj₂ (yᵂ ,
                ( y∈ωx
                , zy≈sy
                ))

            from∞ : ∀ z →
              ((z ≈ᵂ zeroVᵂ) ⊎ (Σ SetUᵂ (λ y → y ∈ᵂ omegaVᵂ × (z ≈ᵂ succVᵂ y)))) →
              z ∈ᵂ omegaVᵂ
            from∞ z hz with hz
            ... | inj₁ z≈z0 = _↔_.from (base-infinity-spec (⌞ z ⌟)) (inj₁ (strip-≈ {x = z} {y = zeroVᵂ} z≈z0))
            ... | inj₂ (y , (y∈ωx , z≈sy)) =
              _↔_.from (base-infinity-spec (⌞ z ⌟))
                (inj₂ (⌞ y ⌟ , (y∈ωx , strip-≈ {x = z} {y = succVᵂ y} z≈sy)))
