{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.RestrictedProduct where

-- Restricted products / “almost everywhere” laws for dependent families.
--
-- This module intentionally does *not* change the dependent boundary carrier
-- `(i : I) → A i`. Instead, it provides law-shaped predicates:
--
-- - “restricted product element”: a family satisfying a local predicate outside
--   a finite (list-indexed) set of exceptions;
-- - “almost everywhere property” for pointwise maps: a family of endomaps
--   preserving (or agreeing with) a reference behaviour outside finitely many
--   indices.
--
-- This is the intended host-minimal hook for “a.e. unramified / restricted
-- product” conditions in distributed-boundary packs: keep locality ultralocal,
-- and quarantine boundary-wide finiteness as an explicit, compositional layer.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.List.Ops using
  ( _++_
  ; _∈_
  ; _∉_
  ; ∈-++-l
  ; ∈-++-r
  ; ∉-++-l
  ; ∉-++-r
  )

-- --------------------------------------------------------------------------
-- Minimal list surface: we reuse the prelude list ops module.

-- --------------------------------------------------------------------------
-- “Almost all” quantifier (list-indexed cofinite condition).

AlmostAll
  : ∀ {ℓI ℓP}
    {I : Set ℓI}
  → (I → Set ℓP)
  → Set (ℓI ⊔ ℓP)
AlmostAll {I = I} P =
  Σ (List I) (λ bad → ∀ i → i ∉ bad → P i)

-- Restricted-product elements: satisfy a local predicate outside finitely many indices.
Restricted
  : ∀ {ℓI ℓA ℓP}
    {I : Set ℓI}
    {A : I → Set ℓA}
  → ((i : I) → A i → Set ℓP)
  → ((i : I) → A i)
  → Set (ℓI ⊔ ℓP)
Restricted Good F = AlmostAll (λ i → Good i (F i))

-- Restrictedness is extensional in the underlying dependent family:
-- pointwise equality transports restrictedness (no function extensionality needed).
restricted-cong
  : ∀ {ℓI ℓA ℓP}
    {I : Set ℓI}
    {A : I → Set ℓA}
    (Good : (i : I) → A i → Set ℓP)
    {F G : (i : I) → A i}
  → (∀ i → F i ≡ G i)
  → Restricted Good F
  → Restricted Good G
restricted-cong Good eq (bad , good) =
  ( bad
  , λ i notin → subst (λ a → Good i a) (eq i) (good i notin)
  )

-- --------------------------------------------------------------------------
-- Pointwise map laws.

-- Pointwise action on dependent families.
pointwise
  : ∀ {ℓI ℓA ℓB}
    {I : Set ℓI}
    {A : I → Set ℓA}
    {B : I → Set ℓB}
  → ((i : I) → A i → B i)
  → ((i : I) → A i)
  → ((i : I) → B i)
pointwise f F i = f i (F i)

-- “Almost everywhere agreement” of pointwise functions (extensional per index).
AEAgree
  : ∀ {ℓI ℓA ℓB}
    {I : Set ℓI}
    {A : I → Set ℓA}
    {B : I → Set ℓB}
  → (f g : (i : I) → A i → B i)
  → Set (ℓI ⊔ ℓA ⊔ ℓB)
AEAgree f g = AlmostAll (λ i → ∀ x → f i x ≡ g i x)

-- Almost-everywhere identity endomap: agree with identity outside finitely many indices.
AETrivial
  : ∀ {ℓI ℓA}
    {I : Set ℓI}
    {A : I → Set ℓA}
  → (f : (i : I) → A i → A i)
  → Set (ℓI ⊔ ℓA)
AETrivial f = AEAgree f (λ i x → x)

AETrivial-id
  : ∀ {ℓI ℓA}
    {I : Set ℓI}
    {A : I → Set ℓA}
  → AETrivial {I = I} {A = A} (λ i x → x)
AETrivial-id = ([] , λ _ _ _ → refl)

AETrivial-comp
  : ∀ {ℓI ℓA}
    {I : Set ℓI}
    {A : I → Set ℓA}
    {f g : (i : I) → A i → A i}
  → AETrivial f
  → AETrivial g
  → AETrivial (λ i x → g i (f i x))
AETrivial-comp {f = f} {g = g} (badF , fId) (badG , gId) =
  (badF ++ badG)
  , λ i notin x →
      trans
        (cong (g i) (fId i (∉-++-l notin) x))
        (gId i (∉-++-r notin) x)

-- “Almost everywhere preservation” of a local predicate.
AEPreserves
  : ∀ {ℓI ℓA ℓP}
    {I : Set ℓI}
    {A : I → Set ℓA}
  → ((i : I) → A i → Set ℓP)
  → (f : (i : I) → A i → A i)
  → Set (ℓI ⊔ ℓA ⊔ ℓP)
AEPreserves Good f = AlmostAll (λ i → ∀ x → Good i x → Good i (f i x))

AEPreserves-id
  : ∀ {ℓI ℓA ℓP}
    {I : Set ℓI}
    {A : I → Set ℓA}
    (Good : (i : I) → A i → Set ℓP)
  → AEPreserves Good (λ i x → x)
AEPreserves-id _ = ([] , λ _ _ _ ok → ok)

AEPreserves-comp
  : ∀ {ℓI ℓA ℓP}
    {I : Set ℓI}
    {A : I → Set ℓA}
    {f g : (i : I) → A i → A i}
    (Good : (i : I) → A i → Set ℓP)
  → AEPreserves Good f
  → AEPreserves Good g
  → AEPreserves Good (λ i x → g i (f i x))
AEPreserves-comp {f = f} {g = g} Good (badF , presF) (badG , presG) =
  (badF ++ badG)
  , λ i notin x ok →
      presG i (∉-++-r notin) (f i x) (presF i (∉-++-l notin) x ok)

-- If a family is restricted and the pointwise endomap preserves the local
-- predicate almost everywhere, then the image family is restricted.
restricted-map
  : ∀ {ℓI ℓA ℓP}
    {I : Set ℓI}
    {A : I → Set ℓA}
    (Good : (i : I) → A i → Set ℓP)
    (f : (i : I) → A i → A i)
  → AEPreserves Good f
  → ∀ {F}
  → Restricted Good F
  → Restricted Good (pointwise f F)
restricted-map Good f (badP , pres) {F = F} (badR , good) =
  (badR ++ badP)
  , λ i notin →
      pres i (∉-++-r notin) (F i) (good i (∉-++-l notin))
