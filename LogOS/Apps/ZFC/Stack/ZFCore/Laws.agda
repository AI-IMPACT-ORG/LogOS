{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.Laws where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.View using (μ)

open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)
import LogOS.Apps.ZFC.Stack.ZFCore.Signature as Signature
open Signature using
  ( ZFSignatureCore
  ; ZFSignaturePowerset
  ; ZFSignatureOmega
  ; ZFSignatureSeparation
  ; ZFSignatureReplacement
  ; ZFSignature
  )

-- ------------------------------------------------------------------------
-- Law profiles (matching the signature profiles)

record ZFLawsCore {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignatureCore C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignatureCore Sig
  field
    empty-spec
      : ∀ z → ¬ (z ∈ μ EmptyV tt)

    pairing-spec
      : ∀ x y z
      → (z ∈ μ PairV (x , y)) ↔ ((z ≈ x) ⊎ (z ≈ y))

    union-spec
      : ∀ x z
      → (z ∈ μ UnionV x) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y)))

-- Derived membership spec for successor (`SuccV`) from the core profile.
succ-spec-from-core
  : ∀ {ℓ : Level} {C : SetContext {ℓ}}
  → (Sig : ZFSignatureCore C)
  → ZFLawsCore C Sig
  → let open SetContext C in
    ∀ x z
    → (z ∈ μ (Signature.DerivedCore.SuccV Sig) x) ↔ ((z ∈ x) ⊎ (z ≈ x))
succ-spec-from-core {ℓ} {C} Sig laws x z =
  intro (to z) (from z)
  where
    open SetContext C
    open ZFSignatureCore Sig
    open ZFLawsCore laws
    module D = Signature.DerivedCore Sig

    singleton : SetU → SetU
    singleton a = μ D.singletonV a

    union₂ : SetU → SetU → SetU
    union₂ a b = μ D.union₂V (a , b)

    mem-singleton↔ : ∀ {a w} → (w ∈ singleton a) ↔ (w ≈ a)
    mem-singleton↔ {a} {w} =
      let p = pairing-spec a a w in
      intro
        (λ w∈ →
          let e = _↔_.to p w∈ in
          elim e)
        (λ wa → _↔_.from p (inj₁ wa))
      where
        elim : ∀ {A : Set ℓ} → (A ⊎ A) → A
        elim (inj₁ a) = a
        elim (inj₂ a) = a

    to : ∀ w → w ∈ union₂ x (singleton x) → (w ∈ x) ⊎ (w ≈ x)
    to w w∈ with _↔_.to (union-spec (μ PairV (x , singleton x)) w) w∈
    ... | (y , (y∈pair , w∈y)) with _↔_.to (pairing-spec x (singleton x) y) y∈pair
    ... | inj₁ y≈x = inj₁ (fst y≈x w w∈y)
    ... | inj₂ y≈s =
      inj₂ (_↔_.to mem-singleton↔ (fst y≈s w w∈y))

    from : ∀ w → (w ∈ x ⊎ w ≈ x) → w ∈ union₂ x (singleton x)
    from w (inj₁ w∈x) =
      _↔_.from (union-spec (μ PairV (x , singleton x)) w)
        ( x
        , ( _↔_.from (pairing-spec x (singleton x) x) (inj₁ (refl≈ x))
          , w∈x
          )
        )
    from w (inj₂ w≈x) =
      _↔_.from (union-spec (μ PairV (x , singleton x)) w)
        ( singleton x
        , ( _↔_.from (pairing-spec x (singleton x) (singleton x)) (inj₂ (refl≈ (singleton x)))
          , _↔_.from mem-singleton↔ w≈x
          )
        )

record ZFLawsPowerset {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignaturePowerset C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignaturePowerset Sig
  field
    powerset-spec
      : ∀ x z
      → (z ∈ μ PowersetV x) ↔ (∀ w → w ∈ z → w ∈ x)

record ZFLawsInfinity
  {ℓ : Level}
  (C : SetContext {ℓ})
  (Core : ZFSignatureCore C)
  (Ω : ZFSignatureOmega C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignatureOmega Ω
  field
    infinity-spec
      : ∀ z
      → (z ∈ μ OmegaV tt)
          ↔ ((z ≈ μ (Signature.DerivedCore.ZeroV Core) tt)
            ⊎ (Σ SetU (λ y → y ∈ μ OmegaV tt × (z ≈ μ (Signature.DerivedCore.SuccV Core) y))))

record ZFLawsSeparation {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignatureSeparation C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignatureSeparation Sig
  field
    separation-spec
      : ∀ (P : SetU → Set ℓ) x z
      → (z ∈ μ (SeparationV P) x) ↔ ((z ∈ x) × (P z))

record ZFLawsReplacement {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignatureReplacement C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignatureReplacement Sig
  field
    replacement-spec
      : ∀ (R : SetU → SetU → Set ℓ) x z
      → (z ∈ μ (ReplacementV R) x) ↔ (Σ SetU (λ u → u ∈ x × R u z))

record ZFLawsFoundation {ℓ : Level} (C : SetContext {ℓ}) (Core : ZFSignatureCore C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignatureCore Core
  field
    foundation
      : ∀ x
      → (Σ SetU (λ y → y ∈ x))
      → (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))

record ZFLaws {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignature C)
  : Set (lsuc ℓ) where
  open ZFSignature Sig
  field
    coreLaws : ZFLawsCore C coreSig
    powersetLaws : ZFLawsPowerset C powSig
    infinityLaws : ZFLawsInfinity C coreSig omegaSig
    separationLaws : ZFLawsSeparation C sepSig
    replacementLaws : ZFLawsReplacement C repSig
    foundationLaws : ZFLawsFoundation C coreSig

  open ZFLawsCore coreLaws public
  open ZFLawsPowerset powersetLaws public
  open ZFLawsInfinity infinityLaws public
  open ZFLawsSeparation separationLaws public
  open ZFLawsReplacement replacementLaws public
  open ZFLawsFoundation foundationLaws public
