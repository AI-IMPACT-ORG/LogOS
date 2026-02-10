{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.InfiniteLemmasShared where

open import LogOS.Prelude
open import LogOS.Minimal.Con

module For
  {ℓ : Level}
  (CP : ConPreorder ℓ)
  (Th⋆ : ConPreorder.Con CP)
  (Endo : Set (lsuc ℓ))
  (fn : Endo → ConPreorder.Con CP → ConPreorder.Con CP)
  (_≤₂_ : Endo → Endo → Set ℓ)
  (toPointwise : ∀ {f g} → _≤₂_ f g → (∀ c → ConPreorder._⊑_ CP (fn f c) (fn g c)))
  (fromPointwise : ∀ {f g} → (∀ c → ConPreorder._⊑_ CP (fn f c) (fn g c)) → _≤₂_ f g)
  (idEndo : Endo)
  (id-at : ∀ c → fn idEndo c ≡ c)
  (_∘E_ : Endo → Endo → Endo)
  (compose-at : ∀ g f c → fn (g ∘E f) c ≡ fn g (fn f c))
  (Flow-Endo : Endo)
  (Flow-closeEndo : Endo → Endo)
  (f≤Flow→fTh⋆≤Th⋆ : (f : Endo) → _≤₂_ f Flow-Endo → ConPreorder._⊑_ CP (fn f Th⋆) Th⋆)
  (Flow≤f→Th⋆≤fTh⋆ : (f : Endo) → _≤₂_ Flow-Endo f → ConPreorder._⊑_ CP Th⋆ (fn f Th⋆))
  (id≤Flow-close : (f : Endo) → _≤₂_ idEndo f → _≤₂_ idEndo (Flow-closeEndo f))
  (Flow-close≤Flow : (f : Endo) → _≤₂_ f Flow-Endo → _≤₂_ (Flow-closeEndo f) Flow-Endo)
  (flow-mono : ∀ {x y} → ConPreorder._⊑_ CP x y → ConPreorder._⊑_ CP (fn Flow-Endo x) (fn Flow-Endo y))
  (flow-idemp-lax : ∀ c → ConPreorder._⊑_ CP (fn Flow-Endo (fn Flow-Endo c)) (fn Flow-Endo c))
  where

  private
    module C = ConPreorder CP

  sandwich-bounds-at-Th⋆
    : (f : Endo)
    → _≤₂_ idEndo f
    → _≤₂_ f Flow-Endo
    → (C._⊑_ Th⋆ (fn f Th⋆)) × (C._⊑_ (fn f Th⋆) Th⋆)
  sandwich-bounds-at-Th⋆ f infl f≤tf =
    (subst (λ x → C._⊑_ x (fn f Th⋆)) (id-at Th⋆) (toPointwise infl Th⋆))
    , f≤Flow→fTh⋆≤Th⋆ f f≤tf

  sandwich-fixed-at-Th⋆
    : (f : Endo)
    → _≤₂_ idEndo f
    → _≤₂_ f Flow-Endo
    → _≈CP_ CP (fn f Th⋆) Th⋆
  sandwich-fixed-at-Th⋆ f infl f≤tf =
    let
      p = sandwich-bounds-at-Th⋆ f infl f≤tf
    in
    (≈CP⇐ {CP = CP} p , ≈CP⇒ {CP = CP} p)

  Flow-close-fixed-at-Th⋆
    : (f : Endo)
    → _≤₂_ idEndo f
    → _≤₂_ f Flow-Endo
    → _≈CP_ CP (fn (Flow-closeEndo f) Th⋆) Th⋆
  Flow-close-fixed-at-Th⋆ f infl f≤tf =
    sandwich-fixed-at-Th⋆ (Flow-closeEndo f)
      (id≤Flow-close f infl)
      (Flow-close≤Flow f f≤tf)

  sandwich-compose
    : (f g : Endo)
    → _≤₂_ idEndo f → _≤₂_ f Flow-Endo
    → _≤₂_ idEndo g → _≤₂_ g Flow-Endo
    → _≈CP_ CP (fn (g ∘E f) Th⋆) Th⋆
  sandwich-compose f g inflf f≤flow inflg g≤flow =
    sandwich-fixed-at-Th⋆
      (g ∘E f)
      (fromPointwise (λ c →
        let
          step₁ = toPointwise inflf c
          step₂ = subst (λ x → C._⊑_ x (fn g (fn f c))) (id-at (fn f c)) (toPointwise inflg (fn f c))
          raw = C.trans step₁ step₂
        in
        subst (λ y → C._⊑_ (fn idEndo c) y) (sym (compose-at g f c)) raw))
      (fromPointwise (λ c →
        let
          step₁ = toPointwise g≤flow (fn f c)
          step₂ = flow-mono (toPointwise f≤flow c)
          step₃ = flow-idemp-lax c
          raw = C.trans step₁ (C.trans step₂ step₃)
        in
        subst (λ x → C._⊑_ x (fn Flow-Endo c)) (sym (compose-at g f c)) raw))
