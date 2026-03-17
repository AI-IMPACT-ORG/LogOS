{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat.Reversibility where

open import LogOS.Prelude
open import LogOS.Prelude.FiniteFamily using (at)
open import LogOS.LT.ConPreorder using (Con; _≈_; ≈-sym; ≡→≈; refl⊑)
open import LogOS.LT.Thin2Functor using (mapHom)
open import LogOS.LT.View using (idView; pullbackView)
open import LogOS.LT.View.Factorisation using (mapFactorisation)
open import LogOS.LT.ConPreorder.Isomorphism using
  ( OrderIso
  ; idOrderIso
  ; compOrderIso
  ; mono-≈
  ; orderIso-reflects-≈
  )
  renaming
  ( f to iso-f
  ; f-mono to iso-f-mono
  )
open import LogOS.Ports.Opacity.Distinguishability using
  ( family
  ; separated
  )
open import LogOS.Ports.Opacity.FiniteCompression using
  ( FiniteCompressionWitness
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat.Causality as Causality
import LogOS.Ports.AbstractDeutsch2Cat.Locality as Locality
import LogOS.Ports.LawSlice2Cat as LawSlice

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  open DependentLocalSemantics PS
  module Local = Locality.Deutsch2CatLocal {ℓCode = ℓCode} PS
  module Cau = Causality.Deutsch2CatLocal {ℓCode = ℓCode} PS

  data ReversibleTag : Set where
    reversibleTag : ReversibleTag

  reversibleTagId : ℕ
  reversibleTagId = 12

  -- Explicit unit payload (avoids `⊤`/`tt` footguns in composed stacks).
  record ReversibleOb : Set where
    constructor ttReversible

  -- Local reversibility as a law-port: pointwise order-isomorphisms in each fibre.
  record LocalReversible {A B : Thin2Cat.Obj Cau.WithPort} (h : Con (Thin2Cat.Hom Cau.WithPort A B))
    : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)) where
    field
      isoAt : (i : I) → OrderIso (O i)

      forward≈
        : ∀ i x
        → _≈_ (O i) (iso-f (isoAt i) x) (Local.physicalMapAt (mapHom Cau.forget h) i x)

  idLocalReversible : ∀ {A : Thin2Cat.Obj Cau.WithPort} → LocalReversible (Thin2Cat.id Cau.WithPort {A})
  idLocalReversible =
    record
      { isoAt = λ _ → idOrderIso
      ; forward≈ = λ i x → (refl⊑ (O i) , refl⊑ (O i))
      }

  compLocalReversible
    : ∀ {A B C : Thin2Cat.Obj Cau.WithPort}
      {f : Con (Thin2Cat.Hom Cau.WithPort A B)}
      {g : Con (Thin2Cat.Hom Cau.WithPort B C)}
    → LocalReversible f
    → LocalReversible g
    → LocalReversible (Thin2Cat._∘_ Cau.WithPort g f)
  compLocalReversible {f = f} {g = g} rf rg =
    record
      { isoAt = λ i → compOrderIso (LocalReversible.isoAt rf i) (LocalReversible.isoAt rg i)
      ; forward≈ = λ i x →
          let
            step₁ : _≈_ (O i)
                    (iso-f (LocalReversible.isoAt rg i) (iso-f (LocalReversible.isoAt rf i) x))
                    (iso-f (LocalReversible.isoAt rg i) (Local.physicalMapAt (mapHom Cau.forget f) i x))
            step₁ =
              mono-≈
                {O = O i}
                {f = iso-f (LocalReversible.isoAt rg i)}
                (iso-f-mono (LocalReversible.isoAt rg i))
                (iso-f (LocalReversible.isoAt rf i) x)
                (Local.physicalMapAt (mapHom Cau.forget f) i x)
                (LocalReversible.forward≈ rf i x)

            step₂ : _≈_ (O i)
                    (iso-f (LocalReversible.isoAt rg i) (Local.physicalMapAt (mapHom Cau.forget f) i x))
                    (Local.physicalMapAt (mapHom Cau.forget g) i (Local.physicalMapAt (mapHom Cau.forget f) i x))
            step₂ = LocalReversible.forward≈ rg i (Local.physicalMapAt (mapHom Cau.forget f) i x)
          in
          let
            module R = LogOS.Prelude.RefinementKit.Reasoning (O i)
            open R using (begin≈_; _≈⟨_⟩_; _∎≈)
          in
          begin≈
            iso-f (LocalReversible.isoAt rg i) (iso-f (LocalReversible.isoAt rf i) x)
              ≈⟨ step₁ ⟩
            iso-f (LocalReversible.isoAt rg i) (Local.physicalMapAt (mapHom Cau.forget f) i x)
              ≈⟨ step₂ ⟩
            Local.physicalMapAt (mapHom Cau.forget g) i (Local.physicalMapAt (mapHom Cau.forget f) i x) ∎≈
      }

  localReversible-reflects-≈
    : ∀ {A B : Thin2Cat.Obj Cau.WithPort}
      {h : Con (Thin2Cat.Hom Cau.WithPort A B)}
    → LocalReversible h
    → (i : I)
    → (x y : Con (O i))
    → _≈_ (O i) (Local.physicalMapAt (mapHom Cau.forget h) i x) (Local.physicalMapAt (mapHom Cau.forget h) i y)
    → _≈_ (O i) x y
  localReversible-reflects-≈ {h = h} lr i x y eq =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning (O i)
      open R using (begin≈_; _≈⟨_⟩_; _∎≈)

      iso = LocalReversible.isoAt lr i

      step₁ : _≈_ (O i) (iso-f iso x) (Local.physicalMapAt (mapHom Cau.forget h) i x)
      step₁ = LocalReversible.forward≈ lr i x

      step₂ : _≈_ (O i) (Local.physicalMapAt (mapHom Cau.forget h) i x) (Local.physicalMapAt (mapHom Cau.forget h) i y)
      step₂ = eq

      step₃ : _≈_ (O i) (Local.physicalMapAt (mapHom Cau.forget h) i y) (iso-f iso y)
      step₃ = ≈-sym {CP = O i} (LocalReversible.forward≈ lr i y)

      isoEq : _≈_ (O i) (iso-f iso x) (iso-f iso y)
      isoEq =
        begin≈
          iso-f iso x ≈⟨ step₁ ⟩
          Local.physicalMapAt (mapHom Cau.forget h) i x ≈⟨ step₂ ⟩
          Local.physicalMapAt (mapHom Cau.forget h) i y ≈⟨ step₃ ⟩
          iso-f iso y ∎≈
    in
    orderIso-reflects-≈ iso x y isoEq

  collapse-obstructs-localReversible
    : ∀ {A B : Thin2Cat.Obj Cau.WithPort}
      {h : Con (Thin2Cat.Hom Cau.WithPort A B)}
    → (i : I)
    → (x y : Con (O i))
    → ¬ _≈_ (O i) x y
    → _≈_ (O i) (Local.physicalMapAt (mapHom Cau.forget h) i x) (Local.physicalMapAt (mapHom Cau.forget h) i y)
    → ¬ LocalReversible h
  collapse-obstructs-localReversible {h = h} i x y x≉y fx≈fy lr =
    x≉y (localReversible-reflects-≈ {h = h} lr i x y fx≈fy)

  physicalFactorisation
    : ∀ {A B : Thin2Cat.Obj Cau.WithPort}
    → (h : Con (Thin2Cat.Hom Cau.WithPort A B))
    → (region : I)
    → LogOS.LT.View.Factorisation.FactorisesThrough
        (idView (O region))
        (pullbackView (Local.physicalMapAt (mapHom Cau.forget h) region) (idView (O region)))
  physicalFactorisation h region =
    mapFactorisation
      (Local.physicalMapAt (mapHom Cau.forget h) region)
      (Local.physicalMonoAt (mapHom Cau.forget h) region)

  localReversible-noFiniteCompression
    : ∀ {A B : Thin2Cat.Obj Cau.WithPort}
      {h : Con (Thin2Cat.Hom Cau.WithPort A B)}
    → (region : I)
    → LocalReversible h
    → ¬ FiniteCompressionWitness (physicalFactorisation h region)
  localReversible-noFiniteCompression {h = h} region lr fc =
    separated (FiniteCompressionWitness.source fc)
      (FiniteCompressionWitness.i fc)
      (FiniteCompressionWitness.k fc)
      (FiniteCompressionWitness.distinct fc)
      (localReversible-reflects-≈ lr region x y images≈)
    where
      module R = LogOS.Prelude.RefinementKit.Reasoning (O region)
      open R using (begin≈_; _≈⟨_⟩_; _∎≈)

      S = family (FiniteCompressionWitness.source fc)
      T = family (FiniteCompressionWitness.target fc)

      x : Con (O region)
      x = at S (FiniteCompressionWitness.i fc)

      y : Con (O region)
      y = at S (FiniteCompressionWitness.k fc)

      sound-i
        : _≈_ (O region)
            (Local.physicalMapAt (mapHom Cau.forget h) region
              (at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.i fc))))
            (Local.physicalMapAt (mapHom Cau.forget h) region x)
      sound-i = FiniteCompressionWitness.sound fc (FiniteCompressionWitness.i fc)

      sound-k
        : _≈_ (O region)
            (Local.physicalMapAt (mapHom Cau.forget h) region
              (at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.k fc))))
            (Local.physicalMapAt (mapHom Cau.forget h) region y)
      sound-k = FiniteCompressionWitness.sound fc (FiniteCompressionWitness.k fc)

      sameTarget≡
        : at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.i fc))
          ≡
          at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.k fc))
      sameTarget≡ =
        cong
          (at T)
          (FiniteCompressionWitness.merged fc)

      sameTarget≈
        : _≈_ (O region)
            (Local.physicalMapAt (mapHom Cau.forget h) region
              (at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.i fc))))
            (Local.physicalMapAt (mapHom Cau.forget h) region
              (at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.k fc))))
      sameTarget≈ =
        ≡→≈ {CP = O region}
          (cong (Local.physicalMapAt (mapHom Cau.forget h) region) sameTarget≡)

      images≈ : _≈_ (O region)
                  (Local.physicalMapAt (mapHom Cau.forget h) region x)
                  (Local.physicalMapAt (mapHom Cau.forget h) region y)
      images≈ =
        begin≈
          Local.physicalMapAt (mapHom Cau.forget h) region x
            ≈⟨ ≈-sym {CP = O region} sound-i ⟩
          Local.physicalMapAt (mapHom Cau.forget h) region
            (at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.i fc)))
            ≈⟨ sameTarget≈ ⟩
          Local.physicalMapAt (mapHom Cau.forget h) region
            (at T (FiniteCompressionWitness.assign fc (FiniteCompressionWitness.k fc)))
            ≈⟨ sound-k ⟩
          Local.physicalMapAt (mapHom Cau.forget h) region y ∎≈

  module Port =
    LawSlice.Exports
      {C = Cau.WithPort}
      {Tag = ReversibleTag}
      reversibleTagId
      ReversibleOb
      (λ {A} {B} (h : Con (Thin2Cat.Hom Cau.WithPort A B)) → LocalReversible h)
      idLocalReversible
      compLocalReversible

  port2Cat : LawSlice.Singleton2Cat Cau.WithPort reversibleTagId ReversibleTag
  port2Cat =
    Port.port2Cat

  open Port public using (singleton; stack; port; Displayed; WithPort; forget)
