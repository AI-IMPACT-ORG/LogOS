{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.Obstruction where

-- Opaque families and obstruction to family-local public readback.

open import LogOS.Prelude
open import LogOS.Prelude.Fin using (Fin; _≢_)
open import LogOS.Ports.Opacity.Distinguishability using
  ( ObservedFamily
  ; DistinguishableFamily
  ; family
  ; separated
  ; size
  ; at
  )
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; MonoMap
  ; monoMap-≈
  ; _≈_
  ; ≈-sym
  )
open import LogOS.LT.View using (View; μ; _≈[_]_)
open import LogOS.LT.View.Factorisation using (FactorisesThrough)

record OpaqueFamily
  {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
  {X : Set ℓX}
  {O₁ : ConPreorder ℓC₁ ℓR₁}
  {O₂ : ConPreorder ℓC₂ ℓR₂}
  {Vprivate : View X O₁}
  {Vpublic : View X O₂}
  (F : FactorisesThrough Vprivate Vpublic)
  : Set (ℓX ⊔ ℓR₁ ⊔ ℓR₂)
  where
  field
    source : DistinguishableFamily Vprivate
    i k : Fin (size (family source))
    distinct : i ≢ k
    publicCollapsed : at (family source) i ≈[ Vpublic ] at (family source) k

open OpaqueFamily public

record PublicReadbackOn
  {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
  {X : Set ℓX}
  {O₁ : ConPreorder ℓC₁ ℓR₁}
  {O₂ : ConPreorder ℓC₂ ℓR₂}
  (S : ObservedFamily X)
  (Vprivate : View X O₁)
  (Vpublic : View X O₂)
  : Set (ℓX ⊔ ℓC₁ ⊔ ℓR₁ ⊔ ℓC₂ ⊔ ℓR₂)
  where
  field
    readback : Con O₂ → Con O₁
    readback-mono : MonoMap O₂ O₁ readback
    soundAt : ∀ i → _≈_ O₁ (readback (μ Vpublic (at S i))) (μ Vprivate (at S i))

open PublicReadbackOn public

record FaithfulPublicObservationOn
  {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
  {X : Set ℓX}
  {O₁ : ConPreorder ℓC₁ ℓR₁}
  {O₂ : ConPreorder ℓC₂ ℓR₂}
  (S : ObservedFamily X)
  (Vprivate : View X O₁)
  (Vpublic : View X O₂)
  : Set (ℓX ⊔ ℓR₁ ⊔ ℓR₂)
  where
  field
    reflectAt
      : ∀ i j
      → at S i ≈[ Vpublic ] at S j
      → at S i ≈[ Vprivate ] at S j

open FaithfulPublicObservationOn public

publicReadback→faithfulPublicObservationOn
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {S : ObservedFamily X}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
  → PublicReadbackOn S Vprivate Vpublic
  → FaithfulPublicObservationOn S Vprivate Vpublic
publicReadback→faithfulPublicObservationOn {O₁ = O₁} {O₂ = O₂} {S = S} {Vprivate = Vprivate} {Vpublic = Vpublic} RB =
  record
    { reflectAt = λ i j public≈ →
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning O₁
          open R using (begin≈_; _≈⟨_⟩_; _∎≈)

          step₁ : _≈_ O₁ (μ Vprivate (at S i)) (readback RB (μ Vpublic (at S i)))
          step₁ = ≈-sym {CP = O₁} (soundAt RB i)

          step₂ : _≈_ O₁ (readback RB (μ Vpublic (at S i))) (readback RB (μ Vpublic (at S j)))
          step₂ =
            monoMap-≈
              {CP₁ = O₂}
              {CP₂ = O₁}
              {f = readback RB}
              (readback-mono RB)
              (μ Vpublic (at S i))
              (μ Vpublic (at S j))
              public≈

          step₃ : _≈_ O₁ (readback RB (μ Vpublic (at S j))) (μ Vprivate (at S j))
          step₃ = soundAt RB j
        in
        begin≈
          μ Vprivate (at S i) ≈⟨ step₁ ⟩
          readback RB (μ Vpublic (at S i)) ≈⟨ step₂ ⟩
          readback RB (μ Vpublic (at S j)) ≈⟨ step₃ ⟩
          μ Vprivate (at S j) ∎≈
    }

opaqueFamily-obstructsPublicReadbackOn
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → ∀ (opq : OpaqueFamily F)
  → ¬ PublicReadbackOn (family (source opq)) Vprivate Vpublic
opaqueFamily-obstructsPublicReadbackOn {Vprivate = Vprivate} {Vpublic = Vpublic} opq RB =
  separated (source opq) (i opq) (k opq) (distinct opq) private≈
  where
    S = family (source opq)

    private≈
      : at S (i opq) ≈[ Vprivate ] at S (k opq)
    private≈ =
      reflectAt
        (publicReadback→faithfulPublicObservationOn RB)
        (i opq)
        (k opq)
        (publicCollapsed opq)

opaqueFamily-obstructsFaithfulPublicObservationOn
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → ∀ (opq : OpaqueFamily F)
  → ¬ FaithfulPublicObservationOn (family (source opq)) Vprivate Vpublic
opaqueFamily-obstructsFaithfulPublicObservationOn {Vprivate = Vprivate} {Vpublic = Vpublic} opq faithful =
  separated (source opq) (i opq) (k opq) (distinct opq)
    (reflectAt faithful (i opq) (k opq) (publicCollapsed opq))
