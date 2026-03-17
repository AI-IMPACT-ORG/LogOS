{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.AbstractGaloisConnection where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Galois connections / adjunctions induce guarded closures (nucleus-style).
--
-- If `L ⊣ R`, then `N = R ∘ L` is a guarded closure:
-- monotone, inflationary, lax-idempotent.
--
-- This is the “boundaries as locales” point: effective semantics as a reflective
-- subspace is not extra structure; it is induced by an adjunction.
--
-- Public-facing note:
-- the theorem statements below use `≼` as an order-flavoured alias for the
-- underlying refinement relation. The kernel preorder itself remains `_⊑_`.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.Syntax.Prop using (_↔_; intro; to; from)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap; refl⊑)
open import LogOS.LT.FunPreorder using (FunPreorder)
open import LogOS.LT.Flow using (GuardedClosure; Stable; mkStable; elem)

record GaloisConnection
  {ℓACon ℓARel ℓBCon ℓBRel : Level}
  (A : ConPreorder ℓACon ℓARel)
  (B : ConPreorder ℓBCon ℓBRel)
  : Set (lsuc (ℓACon ⊔ ℓARel ⊔ ℓBCon ⊔ ℓBRel)) where
  field
    L : Con A → Con B
    R : Con B → Con A

    L-mono : MonoMap A B L
    R-mono : MonoMap B A R

    adj : ∀ a b → _≼_ B (L a) b ↔ _≼_ A a (R b)

open GaloisConnection public
-- Unit/counit derived from `adj`.

unit
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → ∀ a → _≼_ A a (R G (L G a))
unit {A = A} {B = B} G a =
  to (adj G a (L G a)) (refl⊑ B)

counit
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → ∀ b → _≼_ B (L G (R G b)) b
counit {A = A} {B = B} G b =
  from (adj G (R G b) b) (refl⊑ A)

-- The induced closure on A (nucleus-style).
closure
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → GaloisConnection A B
  → GuardedClosure A
closure {A = A} {B = B} G =
  record
    { Flow = λ a → R G (L G a)
    ; mono = λ {x} {y} xy → R-mono G (L-mono G xy)
    ; infl = unit G
    ; idemp-lax = λ a → R-mono G (counit G (L G a))
    }

-- The closure is already fixed on the right image.
closureOnRight≈id
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → ∀ b
  → _≈_ A
      (GuardedClosure.Flow (closure G) (R G b))
      (R G b)
closureOnRight≈id G b =
  ( R-mono G (counit G b)
  , unit G (R G b)
  )

rightImageStable
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → Con B
  → Stable {CP = A} (GuardedClosure.Flow (closure G))
rightImageStable G b =
  mkStable
    (R G b)
    (R-mono G (counit G b))

stable≈rightImage
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → (x : Stable {CP = A} (GuardedClosure.Flow (closure G)))
  → _≈_ A
      (elem x)
      (R G (L G (elem x)))
stable≈rightImage G x =
  ( unit G (elem x)
  , Stable.stable x
  )

stableRepresentation
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → (x : Stable {CP = A} (GuardedClosure.Flow (closure G)))
  → Σ (Con B) (λ b → _≈_ A (elem x) (R G b))
stableRepresentation G x =
  L G (elem x) , stable≈rightImage G x

-- Reflective-image reading:
-- stable points of the induced closure are precisely points in the right image,
-- up to the ambient refinement-equivalence `≈`.

RightImagePoint
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → GaloisConnection A B
  → Con A
  → Set (ℓARel ⊔ ℓBCon)
RightImagePoint {A = A} {B = B} G a =
  Σ (Con B) (λ b → _≈_ A a (R G b))

rightImagePointStable
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → ∀ b
  → RightImagePoint G (R G b)
rightImagePointStable {A = A} G b =
  b , (refl⊑ A , refl⊑ A)

stableReflectiveImage
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → (x : Stable {CP = A} (GuardedClosure.Flow (closure G)))
  → RightImagePoint G (elem x)
stableReflectiveImage G =
  stableRepresentation G

record ReflectiveImageTheorem
  {ℓACon ℓARel ℓBCon ℓBRel : Level}
  {A : ConPreorder ℓACon ℓARel}
  {B : ConPreorder ℓBCon ℓBRel}
  (G : GaloisConnection A B)
  : Set (lsuc (ℓACon ⊔ ℓARel ⊔ ℓBCon ⊔ ℓBRel)) where
  field
    theorem-closureOnRight≈id
      : ∀ b
      → _≈_ A
          (GuardedClosure.Flow (closure G) (R G b))
          (R G b)

    theorem-rightImageStable
      : Con B
      → Stable {CP = A} (GuardedClosure.Flow (closure G))

    theorem-stable≈rightImage
      : (x : Stable {CP = A} (GuardedClosure.Flow (closure G)))
      → _≈_ A
          (elem x)
          (R G (L G (elem x)))

    theorem-stableRepresentation
      : (x : Stable {CP = A} (GuardedClosure.Flow (closure G)))
      → Σ (Con B) (λ b → _≈_ A (elem x) (R G b))

    theorem-stableReflectiveImage
      : (x : Stable {CP = A} (GuardedClosure.Flow (closure G)))
      → RightImagePoint G (elem x)

reflectiveImageTheorem
  : ∀ {ℓACon ℓARel ℓBCon ℓBRel}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → (G : GaloisConnection A B)
  → ReflectiveImageTheorem G
reflectiveImageTheorem G =
  record
    { theorem-closureOnRight≈id = closureOnRight≈id G
    ; theorem-rightImageStable = rightImageStable G
    ; theorem-stable≈rightImage = stable≈rightImage G
    ; theorem-stableRepresentation = stableRepresentation G
    ; theorem-stableReflectiveImage = stableReflectiveImage G
    }

-- Local-to-global lift: pointwise Galois connections on the local interface
-- induce a Galois connection on the distributed boundary `I → _`.
pointwiseGalois
  : ∀ {ℓI ℓACon ℓARel ℓBCon ℓBRel}
    {I : Set ℓI}
    {A : ConPreorder ℓACon ℓARel}
    {B : ConPreorder ℓBCon ℓBRel}
  → GaloisConnection A B
  → GaloisConnection (FunPreorder I A) (FunPreorder I B)
pointwiseGalois {I = I} {A = A} {B = B} G =
  record
    { L = λ F i → L G (F i)
    ; R = λ H i → R G (H i)
    ; L-mono = λ {F} {G'} FG i → L-mono G (FG i)
    ; R-mono = λ {H} {J} HJ i → R-mono G (HJ i)
    ; adj =
        λ F H →
          intro
            (λ LH i → to (adj G (F i) (H i)) (LH i))
            (λ FR i → from (adj G (F i) (H i)) (FR i))
    }
