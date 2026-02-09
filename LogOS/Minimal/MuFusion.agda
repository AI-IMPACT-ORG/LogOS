{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.MuFusion where

-- μ-fusion / naturality for Kleene μ (least pre-fixed points).
--
-- Core idea:
-- if a map between ωCPO preorders preserves ⊥ and ω-sups (for chains) and commutes
-- laxly with an operator, then it transports the Kleene μ construction as an
-- inequality `map (μ F) ⊑ μ G`.
--
-- This module is the minimal-layer “core”: it provides the ωCPO-map structure
-- and the μ-fusion lemma. Higher-level corollaries (e.g. transporting `Th*`,
-- kernel-specialised upgrade constructors) live in `LogOS.Theorems.*`.

open import LogOS.Prelude
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

module For
  {ℓ₁ ℓ₂ : Level}
  (CP₁ : ConPreorder ℓ₁)
  (CP₂ : ConPreorder ℓ₂)
  where

  module GC₁ = Truth.GuardedCore {ℓ = ℓ₁}
  module GC₂ = Truth.GuardedCore {ℓ = ℓ₂}

  open ConPreorder CP₁ renaming (Con to Con₁; _⊑_ to _⊑₁_; trans to trans₁; refl to refl₁) public
  open ConPreorder CP₂ renaming (Con to Con₂; _⊑_ to _⊑₂_; trans to trans₂; refl to refl₂) public

  record OmegaCPOMap
    (ω₁ : GC₁.OmegaCPO CP₁)
    (ω₂ : GC₂.OmegaCPO CP₂)
    (map : Con₁ → Con₂)
    : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    open GC₁.OmegaCPO ω₁ renaming (⊥ to ⊥₁; supω to supω₁)
    open GC₂.OmegaCPO ω₂ renaming (⊥ to ⊥₂; supω to supω₂)
    field
      mono-map : MonoMap CP₁ CP₂ map
      strict⊥  : _⊑₂_ (map ⊥₁) ⊥₂

      -- Scott continuity for maps between ωCPO preorders (lax, ω-chain only).
      cont-ω
        : ∀ (f : ℕ → Con₁)
          (mono-chain : ∀ n → _⊑₁_ (f n) (f (suc n)))
        → _⊑₂_ (map (supω₁ f)) (supω₂ (λ n → map (f n)))

  -- Convenience: build an `OmegaCPOMap` from equalities (common when the map is
  -- definitional or transported through an isomorphism).

  mkOmegaCPOMap≡
    : ∀ {ω₁ : GC₁.OmegaCPO CP₁} {ω₂ : GC₂.OmegaCPO CP₂}
      {map : Con₁ → Con₂}
    → MonoMap CP₁ CP₂ map
    → (map⊥≡ : let open GC₁.OmegaCPO ω₁ renaming (⊥ to ⊥₁)
                   open GC₂.OmegaCPO ω₂ renaming (⊥ to ⊥₂)
              in map ⊥₁ ≡ ⊥₂)
    → (map-supω≡
        : let open GC₁.OmegaCPO ω₁ renaming (supω to supω₁)
              open GC₂.OmegaCPO ω₂ renaming (supω to supω₂)
          in ∀ (f : ℕ → Con₁)
               (mono-chain : ∀ n → _⊑₁_ (f n) (f (suc n)))
             → map (supω₁ f) ≡ supω₂ (λ n → map (f n)))
    → OmegaCPOMap ω₁ ω₂ map
  mkOmegaCPOMap≡ {ω₁ = ω₁} {ω₂ = ω₂} {map = map} monoMap map⊥≡ map-supω≡ =
    record
      { mono-map = monoMap
      ; strict⊥  =
          let open GC₁.OmegaCPO ω₁ renaming (⊥ to ⊥₁)
              open GC₂.OmegaCPO ω₂ renaming (⊥ to ⊥₂)
          in
          subst (λ x → _⊑₂_ (map ⊥₁) x) map⊥≡ refl₂
      ; cont-ω   = λ f mono-chain →
          let open GC₁.OmegaCPO ω₁ renaming (supω to supω₁)
              open GC₂.OmegaCPO ω₂ renaming (supω to supω₂)
          in
          subst (λ x → _⊑₂_ (map (supω₁ f)) x) (map-supω≡ f mono-chain) refl₂
      }

  μ-fusion≤
    : ∀ {ω₁ : GC₁.OmegaCPO CP₁} {ω₂ : GC₂.OmegaCPO CP₂}
      {map : Con₁ → Con₂}
      (M : OmegaCPOMap ω₁ ω₂ map)
      (F : Con₁ → Con₁)
      (G : Con₂ → Con₂)
    → (monoG : MonoOn CP₂ G)
    → (inflF : ∀ c → _⊑₁_ c (F c))
    → (comm  : ∀ c → _⊑₂_ (map (F c)) (G (map c)))
    → _⊑₂_
        (map (GC₁.Kleene.μ ω₁ F))
        (GC₂.Kleene.μ ω₂ G)
  μ-fusion≤ {ω₁ = ω₁} {ω₂ = ω₂} {map = map} M F G monoG inflF comm =
    trans₂ mapμ≤sup-map-iter sup-map-iter≤μ
    where
      open OmegaCPOMap M
      open GC₁.OmegaCPO ω₁ renaming (⊥ to ⊥₁; supω to supω₁)
      open GC₂.OmegaCPO ω₂ renaming (⊥ to ⊥₂; supω to supω₂; ub to ub₂; least to least₂)

      module K₁ = GC₁.Kleene ω₁
      module K₂ = GC₂.Kleene ω₂

      iter₁ = K₁.iter F
      iter₂ = K₂.iter G

      iter₁-mono-chain : ∀ n → _⊑₁_ (iter₁ n) (iter₁ (suc n))
      iter₁-mono-chain = K₁.iter-mono-chain-infl F inflF

      iter-map≤iter
        : ∀ n → _⊑₂_ (map (iter₁ n)) (iter₂ n)
      iter-map≤iter zero = strict⊥
      iter-map≤iter (suc n) =
        trans₂
          (comm (iter₁ n))
          (monoG (iter-map≤iter n))

      mapμ≤sup-map-iter
        : _⊑₂_ (map (K₁.μ F)) (supω₂ (λ n → map (iter₁ n)))
      mapμ≤sup-map-iter =
        cont-ω iter₁ iter₁-mono-chain

      sup-map-iter≤μ
        : _⊑₂_ (supω₂ (λ n → map (iter₁ n))) (K₂.μ G)
      sup-map-iter≤μ =
        least₂ (λ n → map (iter₁ n)) (K₂.μ G) (λ n → trans₂ (iter-map≤iter n) (ub₂ iter₂ n))

-- -------------------------------------------------------------------------
-- OmegaCPOMap infrastructure (identity/composition).
-- -------------------------------------------------------------------------

module Endo {ℓ : Level} (CP : ConPreorder ℓ) where
  module F = For CP CP
  open F

  idOmegaCPOMap
    : ∀ {ω : GC₁.OmegaCPO CP}
    → OmegaCPOMap ω ω (λ x → x)
  idOmegaCPOMap {ω = ω} =
    record
      { mono-map = idMonoMap {CP = CP}
      ; strict⊥  = ConPreorder.refl CP
      ; cont-ω   = λ _ _ → ConPreorder.refl CP
      }

module Compose
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  (CP₁ : ConPreorder ℓ₁)
  (CP₂ : ConPreorder ℓ₂)
  (CP₃ : ConPreorder ℓ₃)
  where

  module F₁₂ = For CP₁ CP₂
  module F₂₃ = For CP₂ CP₃
  module F₁₃ = For CP₁ CP₃

  open ConPreorder CP₁ renaming (Con to Con₁; _⊑_ to _⊑₁_)
  open ConPreorder CP₂ renaming (Con to Con₂; _⊑_ to _⊑₂_)
  open ConPreorder CP₃ renaming (Con to Con₃; trans to trans₃)

  composeOmegaCPOMap
    : ∀ {ω₁ : F₁₂.GC₁.OmegaCPO CP₁}
        {ω₂ : F₁₂.GC₂.OmegaCPO CP₂}
        {ω₃ : F₂₃.GC₂.OmegaCPO CP₃}
        {map₁₂ : Con₁ → Con₂}
        {map₂₃ : Con₂ → Con₃}
      (M₁₂ : F₁₂.OmegaCPOMap ω₁ ω₂ map₁₂)
      (M₂₃ : F₂₃.OmegaCPOMap ω₂ ω₃ map₂₃)
    → F₁₃.OmegaCPOMap ω₁ ω₃ (λ x → map₂₃ (map₁₂ x))
  composeOmegaCPOMap {ω₁ = ω₁} {ω₂ = ω₂} {ω₃ = ω₃} {map₁₂ = map₁₂} {map₂₃ = map₂₃} M₁₂ M₂₃ =
    record
      { mono-map =
          compMonoMap {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = map₁₂} {g = map₂₃}
            (F₁₂.OmegaCPOMap.mono-map M₁₂)
            (F₂₃.OmegaCPOMap.mono-map M₂₃)
      ; strict⊥ =
          trans₃
            (F₂₃.OmegaCPOMap.mono-map M₂₃ (F₁₂.OmegaCPOMap.strict⊥ M₁₂))
            (F₂₃.OmegaCPOMap.strict⊥ M₂₃)
      ; cont-ω = λ f mono-chain →
          let
            module M₁₂ = F₁₂.OmegaCPOMap M₁₂
            module M₂₃ = F₂₃.OmegaCPOMap M₂₃

            chain₂ : ∀ n → _⊑₂_ (map₁₂ (f n)) (map₁₂ (f (suc n)))
            chain₂ n = M₁₂.mono-map (mono-chain n)
          in
          trans₃
            (M₂₃.mono-map (M₁₂.cont-ω f mono-chain))
            (M₂₃.cont-ω (λ n → map₁₂ (f n)) chain₂)
      }
