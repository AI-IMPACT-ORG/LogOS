{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Dagger where

open import LogOS.Prelude

import LogOS.Theorems.Meta.TruthPositivity as TP

-- Minimal dagger/* structure.
-- This is intentionally tiny: it is only meant to make “positivity via t†⋆t”
-- and “self-adjointness” assumptions stateable in a canonical, literature-aligned
-- way without pulling in operator theory or analysis.

record Dagger {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    dag : A → A
    involutive : ∀ a → dag (dag a) ≡ a

open Dagger public

-- A dagger semigroup: a multiplication plus an involution reversing order.

record DaggerSemigroup {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  infixl 7 _⋆_
  field
    _⋆_    : A → A → A
    dagger : Dagger A
    †-anti : ∀ a b → dag dagger (a ⋆ b) ≡ (dag dagger b) ⋆ (dag dagger a)

open DaggerSemigroup public

-- Canonical “square” element: t†⋆t.

square : ∀ {ℓ} {A : Set ℓ} → DaggerSemigroup A → A → A
square S t = _⋆_ S (dag (DaggerSemigroup.dagger S) t) t

-- Squares are self-adjoint: (t†⋆t)† = (t†⋆t).

square-selfAdjoint
  : ∀ {ℓ} {A : Set ℓ} (S : DaggerSemigroup A)
  → ∀ t → dag (DaggerSemigroup.dagger S) (square S t) ≡ square S t
square-selfAdjoint S t =
  let
    ⋆S    = DaggerSemigroup._⋆_ S
    dagS  = Dagger.dag (DaggerSemigroup.dagger S)
    invol = Dagger.involutive (DaggerSemigroup.dagger S)
    anti  = DaggerSemigroup.†-anti S
  in
  trans (anti (dagS t) t) (cong (λ x → ⋆S (dagS t) x) (invol t))

-- Morphisms preserving dagger (and, optionally, multiplication).

record DaggerHom {ℓA ℓB : Level}
                 {A : Set ℓA} {B : Set ℓB}
                 (DA : Dagger A) (DB : Dagger B)
                 : Set (ℓA ⊔ ℓB) where
  field
    map   : A → B
    †-pres : ∀ a → map (dag DA a) ≡ dag DB (map a)

record DaggerSemigroupHom {ℓA ℓB : Level}
                          {A : Set ℓA} {B : Set ℓB}
                          (SA : DaggerSemigroup A)
                          (SB : DaggerSemigroup B)
                          : Set (ℓA ⊔ ℓB) where
  open DaggerSemigroup SA renaming (_⋆_ to _⋆A_)
  open DaggerSemigroup SB renaming (_⋆_ to _⋆B_)
  open Dagger (dagger SA) renaming (dag to dagA)
  open Dagger (dagger SB) renaming (dag to dagB)
  field
    map    : A → B
    ⋆-pres : ∀ a b → map (a ⋆A b) ≡ (map a) ⋆B (map b)
    †-pres : ∀ a → map (dagA a) ≡ dagB (map a)

square-map
  : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
    (SA : DaggerSemigroup A)
    (SB : DaggerSemigroup B)
    (h  : DaggerSemigroupHom SA SB)
  → ∀ t → DaggerSemigroupHom.map h (square SA t) ≡ square SB (DaggerSemigroupHom.map h t)
square-map SA SB h t =
  let open DaggerSemigroupHom h in
  let open DaggerSemigroup SA renaming (_⋆_ to _⋆A_) in
  let open DaggerSemigroup SB renaming (_⋆_ to _⋆B_) in
  let open Dagger (dagger SA) renaming (dag to dagA) in
  trans (⋆-pres (dagA t) t)
        (cong (λ x → x ⋆B map t) (†-pres t))

-- Quadratic truth-positivity: positivity is asserted for “squares” of observable tests.
-- Forgetting the dagger yields an ordinary TruthPositivity instance with
-- `W-pos′ t = W-pos (t†⋆t)`.

record DaggerTruthPositivity {ℓT ℓW ℓObs : Level} : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  field
    Test       : Set ℓT
    Semigroup  : DaggerSemigroup Test
    W-pos      : Test → Set ℓW
    Observable : Test → Set ℓObs

    positivity : ∀ t → Observable t → W-pos (square Semigroup t)

  -- Derived (dagger-free) TruthPositivity view.
  toTruthPositivity : TP.TruthPositivity {ℓT} {ℓW} {ℓObs}
  toTruthPositivity = record
    { Test       = Test
    ; W-pos      = λ t → W-pos (square Semigroup t)
    ; Observable = Observable
    ; positivity = positivity
    }
