{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.GeneratedSubobject.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Small classifier-generated local subobjects from a presentation's existing
-- generators.
--
-- This is the presentation-side local analogue of the repeated LT move
--
--   admissible data -> generated next object
--
-- used by cumulative displayed hierarchies.
--
-- The intended reading is:
-- - `LocalGenerators` names the existing small generators of a presented object,
-- - `GeneratedSubobjects` packages a way of filtering those generators by a
--   small classifier and rebuilding an object,
-- - `SmallClassifier` is the explicit seam when the semantic predicate you
--   want to filter by is larger than the generator index level but is still
--   represented by a small code,
-- - `generated-spec` is the local membership law for the generated object.
--
-- The canonical contracts are refinement-first: generator recovery and
-- generated-subobject recovery are phrased up to a chosen congruence `_≈_`.
-- The equality-shaped strict records remain available as explicit compatibility
-- data for raw presentations that do not expose congruence-aware recovery
-- directly.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

record StrictLocalGenerators
  {ℓX ℓRel : Level}
  (X : Set ℓX)
  (_∈_ : X → X → Set ℓRel)
  (ℓIx : Level)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓIx)) where
  field
    Ix : X → Set ℓIx

    elemAt
      : (x : X)
      → Ix x
      → X

    memberIn
      : ∀ {x z}
      → (i : Ix x)
      → z ≡ elemAt x i
      → z ∈ x

    memberOut
      : ∀ {x z}
      → z ∈ x
      → Σ (Ix x) (λ i → z ≡ elemAt x i)

record LocalGenerators
  {ℓX ℓRel ℓEq : Level}
  (X : Set ℓX)
  (_∈_ : X → X → Set ℓRel)
  (_≈_ : X → X → Set ℓEq)
  (ℓIx : Level)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓEq ⊔ ℓIx)) where
  field
    strict : StrictLocalGenerators X _∈_ ℓIx

    memberIn≈
      : ∀ {x z}
      → (i : StrictLocalGenerators.Ix strict x)
      → z ≈ StrictLocalGenerators.elemAt strict x i
      → z ∈ x

    memberOut≈
      : ∀ {x z}
      → z ∈ x
      → Σ (StrictLocalGenerators.Ix strict x)
          (λ i → z ≈ StrictLocalGenerators.elemAt strict x i)

  Ix : X → Set ℓIx
  Ix = StrictLocalGenerators.Ix strict

  elemAt
    : (x : X)
    → Ix x
    → X
  elemAt = StrictLocalGenerators.elemAt strict

  memberIn
    : ∀ {x z}
    → (i : Ix x)
    → z ≡ elemAt x i
    → z ∈ x
  memberIn = StrictLocalGenerators.memberIn strict

  memberOut
    : ∀ {x z}
    → z ∈ x
    → Σ (Ix x) (λ i → z ≡ elemAt x i)
  memberOut = StrictLocalGenerators.memberOut strict

open LocalGenerators public using (Ix; elemAt; memberIn; memberIn≈; memberOut; memberOut≈)

strictLocalGenerators
  : ∀
      {ℓX ℓRel ℓEq ℓIx : Level}
      {X : Set ℓX}
      {_∈_ : X → X → Set ℓRel}
      (G : StrictLocalGenerators X _∈_ ℓIx)
      (_≈_ : X → X → Set ℓEq)
  → (∀ {x y} → x ≈ y → x ≡ y)
  → (∀ {x y} → x ≡ y → x ≈ y)
  → LocalGenerators X _∈_ _≈_ ℓIx
strictLocalGenerators G _≈_ extensionality ≡→≈ =
  record
    { strict = G
    ; memberIn≈ = λ i z≈child → StrictLocalGenerators.memberIn G i (extensionality z≈child)
    ; memberOut≈ = λ z∈ →
        let
          pair = StrictLocalGenerators.memberOut G z∈
        in
        proj₁ pair , ≡→≈ (proj₂ pair)
    }

record StrictGeneratedSubobjects
  {ℓX ℓRel ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  (G : StrictLocalGenerators X _∈_ ℓIx)
  (ℓCls : Level)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓIx ⊔ ℓCls)) where
  field
    generate
      : (x : X)
      → (StrictLocalGenerators.Ix G x → Set ℓCls)
      → X

    intoGenerated
      : ∀ {x z}
      → (Q : StrictLocalGenerators.Ix G x → Set ℓCls)
      → (i : StrictLocalGenerators.Ix G x)
      → Q i
      → z ≡ StrictLocalGenerators.elemAt G x i
      → z ∈ generate x Q

    outOfGenerated
      : ∀ {x z}
      → (Q : StrictLocalGenerators.Ix G x → Set ℓCls)
      → z ∈ generate x Q
      → Σ (StrictLocalGenerators.Ix G x)
          (λ i → Q i × (z ≡ StrictLocalGenerators.elemAt G x i))

record GeneratedSubobjects
  {ℓX ℓRel ℓEq ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  {_≈_ : X → X → Set ℓEq}
  (G : LocalGenerators X _∈_ _≈_ ℓIx)
  (ℓCls : Level)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓEq ⊔ ℓIx ⊔ ℓCls)) where
  field
    strict : StrictGeneratedSubobjects (LocalGenerators.strict G) ℓCls

    intoGenerated≈
      : ∀ {x z}
      → (Q : LocalGenerators.Ix G x → Set ℓCls)
      → (i : LocalGenerators.Ix G x)
      → Q i
      → z ≈ LocalGenerators.elemAt G x i
      → z ∈ StrictGeneratedSubobjects.generate strict x Q

    outOfGenerated≈
      : ∀ {x z}
      → (Q : LocalGenerators.Ix G x → Set ℓCls)
      → z ∈ StrictGeneratedSubobjects.generate strict x Q
      → Σ (LocalGenerators.Ix G x)
          (λ i → Q i × (z ≈ LocalGenerators.elemAt G x i))

  generate
    : (x : X)
    → (LocalGenerators.Ix G x → Set ℓCls)
    → X
  generate = StrictGeneratedSubobjects.generate strict

  intoGenerated
    : ∀ {x z}
    → (Q : LocalGenerators.Ix G x → Set ℓCls)
    → (i : LocalGenerators.Ix G x)
    → Q i
    → z ≡ LocalGenerators.elemAt G x i
    → z ∈ generate x Q
  intoGenerated = StrictGeneratedSubobjects.intoGenerated strict

  outOfGenerated
    : ∀ {x z}
    → (Q : LocalGenerators.Ix G x → Set ℓCls)
    → z ∈ generate x Q
    → Σ (LocalGenerators.Ix G x)
        (λ i → Q i × (z ≡ LocalGenerators.elemAt G x i))
  outOfGenerated = StrictGeneratedSubobjects.outOfGenerated strict

open GeneratedSubobjects public using
  ( generate
  ; intoGenerated
  ; intoGenerated≈
  ; outOfGenerated
  ; outOfGenerated≈
  )

strictGeneratedSubobjects
  : ∀
      {ℓX ℓRel ℓEq ℓIx ℓCls : Level}
      {X : Set ℓX}
      {_∈_ : X → X → Set ℓRel}
      {_≈_ : X → X → Set ℓEq}
      (G : LocalGenerators X _∈_ _≈_ ℓIx)
      (S : StrictGeneratedSubobjects (LocalGenerators.strict G) ℓCls)
  → (∀ {x y} → x ≈ y → x ≡ y)
  → (∀ {x y} → x ≡ y → x ≈ y)
  → GeneratedSubobjects G ℓCls
strictGeneratedSubobjects G S extensionality ≡→≈ =
  record
    { strict = S
    ; intoGenerated≈ =
        λ Q i qi z≈child →
          StrictGeneratedSubobjects.intoGenerated S Q i qi (extensionality z≈child)
    ; outOfGenerated≈ =
        λ Q z∈ →
          let i , (qi , eq) = StrictGeneratedSubobjects.outOfGenerated S Q z∈
          in
          i , (qi , ≡→≈ eq)
    }

record SmallClassifier
  {ℓX ℓRel ℓEq ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  {_≈_ : X → X → Set ℓEq}
  (G : LocalGenerators X _∈_ _≈_ ℓIx)
  (ℓCls ℓProp : Level)
  (P : (x : X) → LocalGenerators.Ix G x → Set ℓProp)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓEq ⊔ ℓIx ⊔ ℓCls ⊔ ℓProp)) where
  field
    code
      : (x : X)
      → LocalGenerators.Ix G x
      → Set ℓCls

    code-spec
      : ∀ x i
      → code x i ↔ P x i

open SmallClassifier public using (code; code-spec)

classifiedGenerate
  : ∀
      {ℓX ℓRel ℓEq ℓIx ℓCls ℓProp : Level}
      {X : Set ℓX}
      {_∈_ : X → X → Set ℓRel}
      {_≈_ : X → X → Set ℓEq}
      {G : LocalGenerators X _∈_ _≈_ ℓIx}
      {P : (x : X) → LocalGenerators.Ix G x → Set ℓProp}
  → (S : GeneratedSubobjects G ℓCls)
  → SmallClassifier G ℓCls ℓProp P
  → (x : X)
  → X
classifiedGenerate S C x = GeneratedSubobjects.generate S x (SmallClassifier.code C x)

module For
  {ℓX ℓRel ℓEq ℓIx ℓCls : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  {_≈_ : X → X → Set ℓEq}
  (G : LocalGenerators X _∈_ _≈_ ℓIx)
  (S : GeneratedSubobjects G ℓCls)
  where

  module LG = LocalGenerators G
  module GS = GeneratedSubobjects S

  generated-spec
    : ∀ {x z}
    → (Q : LG.Ix x → Set ℓCls)
    → z ∈ GS.generate x Q
        ↔ Σ (LG.Ix x) (λ i → Q i × (z ≈ LG.elemAt x i))
  generated-spec Q =
    intro
      (GS.outOfGenerated≈ Q)
      (λ { (i , (qi , eq)) → GS.intoGenerated≈ Q i qi eq })

module StrictFor
  {ℓX ℓRel ℓIx ℓCls : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  (G : StrictLocalGenerators X _∈_ ℓIx)
  (S : StrictGeneratedSubobjects G ℓCls)
  where

  module LG = StrictLocalGenerators G
  module GS = StrictGeneratedSubobjects S

  generated-spec
    : ∀ {x z}
    → (Q : LG.Ix x → Set ℓCls)
    → z ∈ GS.generate x Q
        ↔ Σ (LG.Ix x) (λ i → Q i × (z ≡ LG.elemAt x i))
  generated-spec Q =
    intro
      (GS.outOfGenerated Q)
      (λ { (i , (qi , eq)) → GS.intoGenerated Q i qi eq })

module WithClassifier
  {ℓX ℓRel ℓEq ℓIx ℓCls ℓProp : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  {_≈_ : X → X → Set ℓEq}
  (G : LocalGenerators X _∈_ _≈_ ℓIx)
  (S : GeneratedSubobjects G ℓCls)
  {P : (x : X) → LocalGenerators.Ix G x → Set ℓProp}
  (C : SmallClassifier G ℓCls ℓProp P)
  where

  module LG = LocalGenerators G
  module GS = GeneratedSubobjects S
  module SC = SmallClassifier C
  module Base = For G S

  generated-classified-spec
    : ∀ {x z}
    → z ∈ classifiedGenerate S C x
        ↔ Σ (LG.Ix x) (λ i → P x i × (z ≈ LG.elemAt x i))
  generated-classified-spec {x} =
    intro
      to
      from
    where
      to
        : ∀ {z}
        → z ∈ classifiedGenerate S C x
        → Σ (LG.Ix x) (λ i → P x i × (z ≈ LG.elemAt x i))
      to z∈ with _↔_.to (Base.generated-spec (SC.code x)) z∈
      ... | (i , (ci , eq)) = i , (_↔_.to (SC.code-spec x i) ci , eq)

      from
        : ∀ {z}
        → Σ (LG.Ix x) (λ i → P x i × (z ≈ LG.elemAt x i))
        → z ∈ classifiedGenerate S C x
      from (i , (pi , eq)) =
        _↔_.from (Base.generated-spec (SC.code x))
          (i , (_↔_.from (SC.code-spec x i) pi , eq))
