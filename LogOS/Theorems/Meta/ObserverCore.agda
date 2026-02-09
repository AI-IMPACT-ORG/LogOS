{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ObserverCore where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; to; from; ¬_)
open import LogOS.Prelude using (Σ; _,_; _×_)
open import LogOS.Minimal.Con using (ConPreorder; _≈CP_)
open import LogOS.Minimal.RelPreorder as RP using (EqRelPreorder)
import LogOS.Minimal.View as View

-- Generic “observer semantics” core:
-- - a code language `Code`,
-- - a decode view `decode : Code → Dec`,
-- - a one-step dynamics `step : Code → Code`,
-- - and a chosen truth predicate `TruthK : Code → Set`.
--
-- The key structural discipline is decode-extensionality: properties only
-- depend on the decoded semantics, not on the concrete code representation.

DecodeExtensional
  : ∀ {ℓCode ℓDec ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (P : Code → Set ℓP)
  → Set (ℓCode ⊔ ℓDec ⊔ ℓP)
DecodeExtensional {Code = Code} {Dec = Dec} decode P =
  let
    decodeView : View.View Code (EqRelPreorder Dec)
    decodeView = record { μ = decode }
  in
  View.Extensional≃ decodeView P

-- Decode-extensionality, but phrased relative to an *observational* equality
-- relation on decoded semantics (typically mutual refinement `≈` in a preorder).
--
-- This is useful for quotient-y / antisymmetry-free models where definitional
-- equality of decoded objects is too strong, but mutual refinement is the
-- intended notion of sameness.

DecodeExtensional≈
  : ∀ {ℓCode ℓDec ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (P : Code → Set ℓP)
  → Set (ℓCode ⊔ ℓDec ⊔ ℓP)
DecodeExtensional≈ {Code = Code} CP decode P =
  let
    decodeView : View.View Code (View.ConPreorder→RelPreorder CP)
    decodeView = record { μ = decode }
  in
  View.Extensional≈ decodeView P

DecodeExtensional≈-cong
  : ∀ {ℓCode ℓDec ℓP : Level}
    {Code : Set ℓCode}
    {CP : ConPreorder ℓDec}
    {decode : Code → ConPreorder.Con CP}
    {P : Code → Set ℓP}
  → DecodeExtensional≈ CP decode P
  → ∀ {γ₁ γ₂} → _≈CP_ CP (decode γ₁) (decode γ₂) → P γ₁ ↔ P γ₂
DecodeExtensional≈-cong extP eq =
  intro
    (λ p → extP _ _ eq p)
    (λ p →
      let (xy , yx) = eq in
      extP _ _ (yx , xy) p)

StableUnder
  : ∀ {ℓCode ℓP : Level}
    {Code : Set ℓCode}
    (step : Code → Code)
    (P : Code → Set ℓP)
  → Set (ℓCode ⊔ ℓP)
StableUnder step P =
  ∀ γ → P γ ↔ P (step γ)

StableUnder≈-cong-step
  : ∀ {ℓCode ℓDec ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step step′ : Code → Code)
    (P : Code → Set ℓP)
  → (∀ γ → _≈CP_ CP (decode (step γ)) (decode (step′ γ)))
  → DecodeExtensional≈ CP decode P
  → StableUnder step P
  → StableUnder step′ P
StableUnder≈-cong-step CP decode step step′ P eqStep extP stableP γ =
  let
    st = stableP γ
    eq = DecodeExtensional≈-cong {CP = CP} {decode = decode} {P = P} extP (eqStep γ)
  in
  intro
    (λ pγ → to eq (to st pγ))
    (λ pγ′ → from st (from eq pγ′))

record Admissible
  {ℓCode ℓDec ℓT ℓP : Level}
  (Code   : Set ℓCode)
  (Dec    : Set ℓDec)
  (decode : Code → Dec)
  (step   : Code → Code)
  (TruthK : Code → Set ℓT)
  (P      : Code → Set ℓP)
  : Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ ℓP) where
  field
    ext    : DecodeExtensional decode P
    sound  : ∀ {γ} → P γ → TruthK γ
    stable : ∀ γ → P γ ↔ P (step γ)

open Admissible public

-- Variant: admissibility where decode-extensionality is phrased relative to
-- mutual refinement (`≈`) in a chosen decoded preorder.

record Admissible≈
  {ℓCode ℓDec ℓT ℓP : Level}
  (Code   : Set ℓCode)
  (CP     : ConPreorder ℓDec)
  (decode : Code → ConPreorder.Con CP)
  (step   : Code → Code)
  (TruthK : Code → Set ℓT)
  (P      : Code → Set ℓP)
  : Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ ℓP) where
  field
    ext≈   : DecodeExtensional≈ CP decode P
    sound  : ∀ {γ} → P γ → TruthK γ
    stable : ∀ γ → P γ ↔ P (step γ)

open Admissible≈ public using (ext≈)

-- Non-vacuity guard for observer semantics: TruthK is neither trivial nor
-- entirely insensitive to decoding.

record NonVacuousObserver
  {ℓCode ℓDec ℓT : Level}
  (Code   : Set ℓCode)
  (Dec    : Set ℓDec)
  (decode : Code → Dec)
  (TruthK : Code → Set ℓT)
  : Set (ℓCode ⊔ ℓDec ⊔ ℓT) where
  field
    trueWitness  : Σ Code (λ γ → TruthK γ)
    falseWitness : Σ Code (λ γ → ¬ TruthK γ)
    decodeDistinct : Σ Code (λ γ₁ → Σ Code (λ γ₂ →
      let
        decodeView : View.View Code (EqRelPreorder Dec)
        decodeView = record { μ = decode }
      in
      ¬ (View._≃[_]_ γ₁ decodeView γ₂)))

-- “Largest admissible predicate” (a la Comm⋆ / Obs⋆): P⋆ γ holds iff there
-- exists some admissible predicate P that contains γ.
--
-- Universe note: because `Pred⋆` is a `Σ` over predicates `P : Code → Set ℓP`,
-- the result lives one universe higher (in `… ⊔ lsuc ℓP`). This is intentional:
-- setting `ℓP = lsuc ℓ` allows witness-carrying observers (traces/certificates),
-- while setting `ℓP = ℓ` tightens types at the cost of restricting observers.

Pred⋆
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Code → Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ lsuc ℓP)
Pred⋆ {ℓP = ℓP} {Code} {Dec} decode step TruthK γ =
  Σ (Code → Set ℓP) (λ P → Admissible Code Dec decode step TruthK P × P γ)

Pred⋆≈
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Code → Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ lsuc ℓP)
Pred⋆≈ {ℓP = ℓP} {Code} CP decode step TruthK γ =
  Σ (Code → Set ℓP) (λ P → Admissible≈ Code CP decode step TruthK P × P γ)

-- --------------------------------------------------------------------------
-- Derived facts: Pred⋆ is the largest admissible predicate.
-- --------------------------------------------------------------------------

Pred⋆-contains
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
    (P      : Code → Set ℓP)
  → Admissible Code Dec decode step TruthK P
  → ∀ {γ} → P γ → Pred⋆ {ℓP = ℓP} decode step TruthK γ
Pred⋆-contains _ _ _ P AP p = P , (AP , p)

Pred⋆-sound
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → ∀ {γ} → Pred⋆ {ℓP = ℓP} decode step TruthK γ → TruthK γ
Pred⋆-sound _ _ _ (P , (AP , p)) = sound AP p

Pred⋆-ext
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → DecodeExtensional decode (Pred⋆ {ℓP = ℓP} decode step TruthK)
Pred⋆-ext decode step TruthK γ₁ γ₂ eq (P , (AP , p)) =
  P , (AP , ext AP γ₁ γ₂ eq p)

Pred⋆-stable
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → ∀ γ → Pred⋆ {ℓP = ℓP} decode step TruthK γ ↔ Pred⋆ {ℓP = ℓP} decode step TruthK (step γ)
Pred⋆-stable decode step TruthK γ =
  intro
    (λ (P , (AP , p)) → P , (AP , to (stable AP γ) p))
    (λ (P , (AP , p)) → P , (AP , from (stable AP γ) p))

-- --------------------------------------------------------------------------
-- Derived facts (≈-extensional variant): Pred⋆≈ is the largest admissible
-- predicate when decode-extensionality uses mutual refinement.
-- --------------------------------------------------------------------------

Pred⋆≈-contains
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
    (P      : Code → Set ℓP)
  → Admissible≈ Code CP decode step TruthK P
  → ∀ {γ} → P γ → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
Pred⋆≈-contains _ _ _ _ P AP p = P , (AP , p)

Pred⋆≈-sound
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → ∀ {γ} → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ → TruthK γ
Pred⋆≈-sound _ _ _ _ (P , (AP , p)) = Admissible≈.sound AP p

Pred⋆≈-ext
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → DecodeExtensional≈ CP decode (Pred⋆≈ {ℓP = ℓP} CP decode step TruthK)
Pred⋆≈-ext CP decode step TruthK γ₁ γ₂ eq (P , (AP , p)) =
  P , (AP , Admissible≈.ext≈ AP γ₁ γ₂ eq p)

Pred⋆≈-stable
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → ∀ γ →
      Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
      ↔ Pred⋆≈ {ℓP = ℓP} CP decode step TruthK (step γ)
Pred⋆≈-stable CP decode step TruthK γ =
  intro
    (λ (P , (AP , p)) → P , (AP , to (Admissible≈.stable AP γ) p))
    (λ (P , (AP , p)) → P , (AP , from (Admissible≈.stable AP γ) p))

-- Step invariance (up to decoded meaning): if two step functions agree after
-- decoding (up to mutual refinement `≈`), they induce the same largest admissible
-- predicate.

-- Same transport, but where the step agreement is only up to decoded `≈`.

Admissible≈-cong-step
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step step′ : Code → Code)
    (TruthK : Code → Set ℓT)
    (P : Code → Set ℓP)
  → (∀ γ → _≈CP_ CP (decode (step γ)) (decode (step′ γ)))
  → Admissible≈ Code CP decode step TruthK P
  → Admissible≈ Code CP decode step′ TruthK P
Admissible≈-cong-step CP decode step step′ TruthK P eqStep AP =
  record
    { ext≈   = Admissible≈.ext≈ AP
    ; sound  = Admissible≈.sound AP
    ; stable = stable′
    }
  where
    stable′ : ∀ γ → P γ ↔ P (step′ γ)
    stable′ γ =
      let st = Admissible≈.stable AP γ in
      intro
        (λ pγ →
          to (DecodeExtensional≈-cong {CP = CP} {decode = decode} {P = P} (Admissible≈.ext≈ AP) (eqStep γ))
            (to st pγ))
        (λ pγ′ →
          from st
            (from (DecodeExtensional≈-cong {CP = CP} {decode = decode} {P = P} (Admissible≈.ext≈ AP) (eqStep γ))
              pγ′))

Pred⋆≈-cong-step
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step step′ : Code → Code)
    (TruthK : Code → Set ℓT)
  → (∀ γ → _≈CP_ CP (decode (step γ)) (decode (step′ γ)))
  → ∀ {γ}
  → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
    ↔
    Pred⋆≈ {ℓP = ℓP} CP decode step′ TruthK γ
Pred⋆≈-cong-step {ℓP = ℓP} CP decode step step′ TruthK eqStep =
  intro to′ from′
  where
    to′
      : ∀ {γ}
      → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
      → Pred⋆≈ {ℓP = ℓP} CP decode step′ TruthK γ
    to′ (P , (AP , pγ)) =
      P , (Admissible≈-cong-step CP decode step step′ TruthK P eqStep AP , pγ)

    from′
      : ∀ {γ}
      → Pred⋆≈ {ℓP = ℓP} CP decode step′ TruthK γ
      → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
    from′ (P , (AP , pγ)) =
      P , (Admissible≈-cong-step CP decode step′ step TruthK P symEqStep AP , pγ)
      where
        symEqStep : ∀ γ → _≈CP_ CP (decode (step′ γ)) (decode (step γ))
        symEqStep γ =
          let (xy , yx) = eqStep γ in
          (yx , xy)
module StepTransport≈
  {ℓCode ℓDec : Level}
  {Code : Set ℓCode}
  (CP : ConPreorder ℓDec)
  (decode : Code → ConPreorder.Con CP)
  (step step′ : Code → Code)
  (eqStep : ∀ γ → _≈CP_ CP (decode (step γ)) (decode (step′ γ)))
  where

  stableUnder
    : ∀ {ℓP : Level}
      (P : Code → Set ℓP)
    → DecodeExtensional≈ CP decode P
    → StableUnder step P
    → StableUnder step′ P
  stableUnder P extP stableP =
    StableUnder≈-cong-step CP decode step step′ P eqStep extP stableP

  admissible
    : ∀ {ℓT ℓP : Level}
      (TruthK : Code → Set ℓT)
      (P : Code → Set ℓP)
    → Admissible≈ Code CP decode step TruthK P
    → Admissible≈ Code CP decode step′ TruthK P
  admissible TruthK P =
    Admissible≈-cong-step CP decode step step′ TruthK P eqStep

  Pred⋆≈↔
    : ∀ {ℓT ℓP : Level}
      (TruthK : Code → Set ℓT)
    → ∀ {γ}
    → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
      ↔
      Pred⋆≈ {ℓP = ℓP} CP decode step′ TruthK γ
  Pred⋆≈↔ TruthK {γ} =
    Pred⋆≈-cong-step CP decode step step′ TruthK eqStep {γ = γ}

Pred⋆-admissible
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Admissible Code Dec decode step TruthK (Pred⋆ {ℓP = ℓP} decode step TruthK)
Pred⋆-admissible decode step TruthK =
  record
    { ext    = Pred⋆-ext decode step TruthK
    ; sound  = Pred⋆-sound decode step TruthK
    ; stable = Pred⋆-stable decode step TruthK
    }

Pred⋆≈-admissible
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Admissible≈ Code CP decode step TruthK (Pred⋆≈ {ℓP = ℓP} CP decode step TruthK)
Pred⋆≈-admissible CP decode step TruthK =
  record
    { ext≈   = Pred⋆≈-ext CP decode step TruthK
    ; sound  = Pred⋆≈-sound CP decode step TruthK
    ; stable = Pred⋆≈-stable CP decode step TruthK
    }

Pred⋆-largest
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
    (P      : Code → Set ℓP)
  → Admissible Code Dec decode step TruthK P
  → ∀ γ → P γ → Pred⋆ {ℓP = ℓP} decode step TruthK γ
Pred⋆-largest decode step TruthK P AP γ p =
  Pred⋆-contains decode step TruthK P AP p

Pred⋆≈-largest
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode}
    (CP : ConPreorder ℓDec)
    (decode : Code → ConPreorder.Con CP)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
    (P      : Code → Set ℓP)
  → Admissible≈ Code CP decode step TruthK P
  → ∀ γ → P γ → Pred⋆≈ {ℓP = ℓP} CP decode step TruthK γ
Pred⋆≈-largest CP decode step TruthK P AP γ p =
  Pred⋆≈-contains CP decode step TruthK P AP p

-- Safe reflection aliases (generic, semantically polymorphic in TruthK).
-- In the reflection literature, "soundness" is the reflection principle
-- (safe predicates imply truth), and "stability" is the modal safety guard.
--
-- Canonical surface: preorder-safe (`≈`) variant only. The definitional-equality
-- variant is intentionally not exported under “Safe⋆” names to avoid accidental
-- misuse in quotient-y / antisymmetry-free models.

SafeAdmissible≈ = Admissible≈

Safe⋆≈ = Pred⋆≈

safe⋆≈-sound = Pred⋆≈-sound
safe⋆≈-ext = Pred⋆≈-ext
safe⋆≈-stable = Pred⋆≈-stable
safe⋆≈-admissible = Pred⋆≈-admissible
safe⋆≈-largest = Pred⋆≈-largest
