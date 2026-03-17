{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.Profile where

-- Observation profiles and threshold predicates for distinguishability/opacity.

open import LogOS.Prelude
open import LogOS.Prelude.Fin using (Fin; _≢_)
open import LogOS.Syntax.Prop using (_↔_; to; from)
open import LogOS.Ports.Opacity.Distinguishability using
  ( ObservedFamily
  ; size
  ; at
  )
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; Opp)
open import LogOS.LT.View using (View; _≈[_]_)
open import LogOS.LT.View.Factorisation using (FactorisesThrough; factorises-≈)
open import LogOS.Ports.CriticalParameter using (CriticalCut; SharpCut)

record ObservationProfile
  {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
  (X : Set ℓX)
  (T : ConPreorder ℓTCon ℓTRel)
  : Set (lsuc (ℓX ⊔ ℓTCon ⊔ ℓTRel ⊔ ℓOCon ⊔ ℓORel))
  where
  field
    O : Con T → ConPreorder ℓOCon ℓORel
    observe : (t : Con T) → View X (O t)
    weaken : ∀ {t u} → _⊑_ T t u → FactorisesThrough (observe t) (observe u)

open ObservationProfile public

DistinguishableAt
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
  → ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T
  → ObservedFamily X
  → Con T
  → Set ℓORel
DistinguishableAt P S t =
  ∀ i j → i ≢ j → ¬ (at S i ≈[ observe P t ] at S j)

OpaqueAt
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
  → ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T
  → ObservedFamily X
  → Con T
  → Set ℓORel
OpaqueAt P S t =
  Σ (Fin (size S) × Fin (size S))
    (λ { (i , j) → i ≢ j × (at S i ≈[ observe P t ] at S j) })

opaqueAt-mono
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
    {P : ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T}
    {S : ObservedFamily X}
    {t u : Con T}
  → _⊑_ T t u
  → OpaqueAt P S t
  → OpaqueAt P S u
opaqueAt-mono {P = P} {S = S} t≤u ((i , j) , (distinct , collapsed)) =
  (i , j) , (distinct , factorises-≈ (weaken P t≤u) collapsed)

distinguishableAt-antimono
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
    {P : ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T}
    {S : ObservedFamily X}
    {t u : Con T}
  → _⊑_ T t u
  → DistinguishableAt P S u
  → DistinguishableAt P S t
distinguishableAt-antimono {P = P} {S = S} t≤u visibleAtU i j distinct collapsedAtT =
  visibleAtU i j distinct (factorises-≈ (weaken P t≤u) collapsedAtT)

ExactOpacityThreshold
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
  → ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T
  → ObservedFamily X
  → Con T
  → Set _
ExactOpacityThreshold {T = T} P S Λ =
  ∀ t → OpaqueAt P S t ↔ _⊑_ T Λ t

ExactVisibilityThreshold
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
  → ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T
  → ObservedFamily X
  → Con T
  → Set _
ExactVisibilityThreshold {T = T} P S Λ =
  ∀ t → DistinguishableAt P S t ↔ _⊑_ (Opp T) Λ t

CriticalOpacity
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
  → ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T
  → ObservedFamily X
  → Set _
CriticalOpacity {T = T} P S = CriticalCut T (OpaqueAt P S)

CriticalVisibility
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
  → ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T
  → ObservedFamily X
  → Set _
CriticalVisibility {T = T} P S = CriticalCut (Opp T) (DistinguishableAt P S)

exactOpacityThreshold→critical
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
    {P : ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T}
    {S : ObservedFamily X}
    {Λ : Con T}
  → ExactOpacityThreshold P S Λ
  → CriticalOpacity P S
exactOpacityThreshold→critical {T = T} {P = P} {S = S} {Λ = Λ} exact =
  record
    { good-mono = λ {t} {u} t≤u → opaqueAt-mono {P = P} {S = S} {t = t} {u = u} t≤u
    ; Λ = Λ
    ; GoodAbove = λ {t} Λ≤t → from (exact t) Λ≤t
    ; least = λ {cut} cutGood → to (exact cut) (cutGood (ConPreorder.refl T))
    }

exactOpacityThreshold→sharp
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
    {P : ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T}
    {S : ObservedFamily X}
    {Λ : Con T}
  → ExactOpacityThreshold P S Λ
  → SharpCut T (OpaqueAt P S)
exactOpacityThreshold→sharp {T = T} {P = P} {S = S} exact =
  record
    { base = exactOpacityThreshold→critical {T = T} {P = P} {S = S} exact
    ; belowFails = λ {t} (_ , t⋠Λ) opaqueAtT → t⋠Λ (to (exact t) opaqueAtT)
    }

exactVisibilityThreshold→critical
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
    {P : ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T}
    {S : ObservedFamily X}
    {Λ : Con T}
  → ExactVisibilityThreshold P S Λ
  → CriticalVisibility P S
exactVisibilityThreshold→critical {T = T} {P = P} {S = S} {Λ = Λ} exact =
  record
    { good-mono = λ {t} {u} t≤u →
        distinguishableAt-antimono {P = P} {S = S} {t = u} {u = t} t≤u
    ; Λ = Λ
    ; GoodAbove = λ {t} Λ≤t → from (exact t) Λ≤t
    ; least = λ {cut} cutGood → to (exact cut) (cutGood (ConPreorder.refl (Opp T)))
    }

exactVisibilityThreshold→sharp
  : ∀ {ℓX ℓTCon ℓTRel ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {T : ConPreorder ℓTCon ℓTRel}
    {P : ObservationProfile {ℓOCon = ℓOCon} {ℓORel = ℓORel} X T}
    {S : ObservedFamily X}
    {Λ : Con T}
  → ExactVisibilityThreshold P S Λ
  → SharpCut (Opp T) (DistinguishableAt P S)
exactVisibilityThreshold→sharp {T = T} {P = P} {S = S} exact =
  record
    { base = exactVisibilityThreshold→critical {T = T} {P = P} {S = S} exact
    ; belowFails = λ {t} (_ , t⋠Λ) visibleAtT → t⋠Λ (to (exact t) visibleAtT)
    }
