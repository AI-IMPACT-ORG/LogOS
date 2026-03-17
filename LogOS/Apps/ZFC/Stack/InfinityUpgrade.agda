{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.InfinityUpgrade where

-- A lightweight “metalogical” route to the ZF Infinity law:
--
-- Instead of requiring an explicit ω-constructor + membership law in the ZF
-- stack ledger, we can derive an ω object as a greatest fixed point (ν) of the
-- usual successor-closure endomorphism on the membership boundary preorder,
-- provided the boundary supports a small amount of completeness/continuity.
--
-- This does *not* show that Infinity follows from the other ZF axioms. The
-- additional assumptions are explicit (`SigmaDCPO` + σ-co-continuity), matching
-- the “auditable axiom dependency” design stance of LogOS.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.View using (μ)
open import LogOS.LT.ConPreorder using (Opp)
open import LogOS.LT.Sup.FinSup using (HasTop)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO)
import LogOS.LT.Sup.AbstractCoKleene as CoKleene

import LogOS.Apps.ZFC.Stack.ZFCore as ZF

-- This module reuses the "no ω" ZF stack profile from `Stack.ZFCore`.

-- Assumptions for deriving an ω object as a greatest fixed point.
record CoKleeneInfinityAssumptions {ℓ : Level} (S : ZF.ZFStackNoOmega {ℓ})
  : Set (lsuc ℓ) where
  open ZF.ZFStackNoOmega S
  -- Derived constructors used by the “successor closure” endomorphism.
  zeroSet : SetU
  zeroSet = μ EmptyV tt

  singletonSet : SetU → SetU
  singletonSet x = μ PairV (x , x)

  union₂Set : SetU → SetU → SetU
  union₂Set x y = μ UnionV (μ PairV (x , y))

  succSet : SetU → SetU
  succSet x = union₂Set x (singletonSet x)

  -- Successor image of a set (Replacement for the successor graph).
  succImage : SetU → SetU
  succImage X = μ (ReplacementV (λ u z → z ≈ succSet u)) X

  -- The endomorphism F(X) = {0} ∪ succ[X].
  step : SetU → SetU
  step X = union₂Set (singletonSet zeroSet) (succImage X)

  field
    SDᵒᵖ : SigmaDCPO (Opp SetBnd)
    stepCoCont : CoKleene.SigmaCoContinuous SetBnd SDᵒᵖ step

-- Upgrade: build a full `ZFStack` by deriving an ω object and its Infinity law
-- from `CoKleeneInfinityAssumptions`.
zfStackFromCoKleene
  : ∀ {ℓ : Level}
  → (S : ZF.ZFStackNoOmega {ℓ})
  → CoKleeneInfinityAssumptions S
  → ZF.ZFStack {ℓ}
zfStackFromCoKleene {ℓ} S A =
  record
    { ctx = ctx
    ; sig = sig∞
    ; laws = laws∞
    }
  where
    open ZF.ZFStackNoOmega S
    open CoKleeneInfinityAssumptions A
    -- Empty set is top in the reverse-inclusion boundary order.
    topSetBnd : HasTop SetBnd
    topSetBnd =
      record
        { ⊤ᵇ = zeroSet
        ; ⊤ᵇ-greatest =
            λ x z z∈0 → ⊥-elim (empty-spec z z∈0)
        }

    module CK = CoKleene.CoKleeneLocal topSetBnd SDᵒᵖ step stepCoCont

    ω : SetU
    ω = CK.ν

    -- Replace the (unconstrained) ω view by the derived fixed point.
    sig∞ : ZF.ZFSignature ctx
    sig∞ =
      ZF.zfSignature
        (record
          { EmptyV = EmptyV
          ; PairV = PairV
          ; UnionV = UnionV
          })
        (record
          { PowersetV = PowersetV })
        (record
          { OmegaV = record { μ = λ _ → ω } })
        (record
          { SeparationV = SeparationV })
        (record
          { ReplacementV = ReplacementV })

    module D∞ = ZF.Derived sig∞

    mem-singleton↔ : ∀ {x z} → (z ∈ μ D∞.singletonV x) ↔ (z ≈ x)
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

    -- Membership specification for `step` (derived; no additional axioms).
    mem-step↔
      : ∀ (X z : SetU)
      → (z ∈ step X)
          ↔ ((z ≈ μ D∞.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ X × (z ≈ μ D∞.SuccV y))))
    mem-step↔ X z =
      intro (to z) (from z)
      where
        to
          : ∀ z
          → z ∈ step X
          → (z ≈ μ D∞.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ X × (z ≈ μ D∞.SuccV y)))
        to z z∈ with _↔_.to (union-spec (μ PairV (singletonSet zeroSet , succImage X)) z) z∈
        ... | (y , (y∈pair , z∈y)) with _↔_.to (pairing-spec (singletonSet zeroSet) (succImage X) y) y∈pair
        ... | inj₁ y≈0 =
          inj₁ (_↔_.to mem-singleton↔ (fst y≈0 z z∈y))
        ... | inj₂ y≈img with _↔_.to (replacement-spec (λ u w → w ≈ μ D∞.SuccV u) X z) (fst y≈img z z∈y)
        ... | (u , (u∈X , z≈su)) =
          inj₂ (u , (u∈X , z≈su))

        from
          : ∀ z
          → ( (z ≈ μ D∞.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ X × (z ≈ μ D∞.SuccV y))) )
          → z ∈ step X
        from z (inj₁ z≈0) =
          _↔_.from (union-spec (μ PairV (singletonSet zeroSet , succImage X)) z)
            ( singletonSet zeroSet
            , ( _↔_.from (pairing-spec (singletonSet zeroSet) (succImage X) (singletonSet zeroSet))
                  (inj₁ (refl≈ (singletonSet zeroSet)))
              , _↔_.from mem-singleton↔ z≈0
              )
            )
        from z (inj₂ (u , (u∈X , z≈su))) =
          _↔_.from (union-spec (μ PairV (singletonSet zeroSet , succImage X)) z)
            ( succImage X
            , ( _↔_.from (pairing-spec (singletonSet zeroSet) (succImage X) (succImage X))
                  (inj₂ (refl≈ (succImage X)))
              , _↔_.from (replacement-spec (λ v w → w ≈ μ D∞.SuccV v) X z)
                  (u , (u∈X , z≈su))
              )
            )

    infinity-spec
      : ∀ z
      → (z ∈ ω)
          ↔ ((z ≈ μ D∞.ZeroV tt)
            ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ μ D∞.SuccV y))))
    infinity-spec z =
      intro to from
      where
        fix : (step ω) ≈ ω
        fix = snd CK.fν≈ν , fst CK.fν≈ν

        to
          : z ∈ ω
          → (z ≈ μ D∞.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ μ D∞.SuccV y)))
        to z∈ω =
          _↔_.to (mem-step↔ ω z) (snd fix z z∈ω)

        from
          : ( (z ≈ μ D∞.ZeroV tt)
              ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ μ D∞.SuccV y))) )
          → z ∈ ω
        from disj =
          fst fix z (_↔_.from (mem-step↔ ω z) disj)

    laws∞ : ZF.ZFLaws ctx sig∞
    laws∞ =
      record
        { coreLaws =
            record
              { empty-spec = empty-spec
              ; pairing-spec = pairing-spec
              ; union-spec = union-spec
              }
        ; powersetLaws =
            record
              { powerset-spec = powerset-spec }
        ; infinityLaws =
            record
              { infinity-spec = infinity-spec }
        ; separationLaws =
            record
              { separation-spec = separation-spec }
        ; replacementLaws =
            record
              { replacement-spec = replacement-spec }
        ; foundationLaws =
            record
              { foundation = foundation }
        }
