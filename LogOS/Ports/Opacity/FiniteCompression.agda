{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.FiniteCompression where

-- Derived finite compression/count-loss layer for explicit examples.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc; _+_)
open import LogOS.Prelude.Fin using (Fin; _≢_)
open import LogOS.Prelude.Fin.Cardinality using
  ( surjective⇒size≤
  ; surjective+collision⇒suc-target≤source
  )
open import LogOS.Prelude.Nat.Order using (_≤ℕ_; ≤ℕ-refl; ≤ℕ-trans; s≤s)
open import LogOS.Ports.Opacity.Distinguishability using
  ( DistinguishableFamily
  ; family
  ; size
  ; at
  )
open import LogOS.Ports.Opacity.Obstruction using
  ( OpaqueFamily
  ; PublicReadbackOn
  ; FaithfulPublicObservationOn
  ; opaqueFamily-obstructsPublicReadbackOn
  ; opaqueFamily-obstructsFaithfulPublicObservationOn
  )
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; ≡→≈
  ; _≈_
  ; ≈-sym
  )
open import LogOS.LT.View using (View; μ; _≈[_]_)
open import LogOS.LT.View.Factorisation using (FactorisesThrough)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.Ports.Opacity.ObservationAction using (ObservationAction; processFactorisation)

record FiniteCompressionWitness
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
    target : DistinguishableFamily Vpublic
    assign : Fin (size (family source)) → Fin (size (family target))
    sound : ∀ i → at (family target) (assign i) ≈[ Vpublic ] at (family source) i
    surjective : ∀ j → Σ (Fin (size (family source))) (λ i → assign i ≡ j)
    i : Fin (size (family source))
    k : Fin (size (family source))
    distinct : i ≢ k
    merged : assign i ≡ assign k

open FiniteCompressionWitness public

FiniteCompressionOn
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C)
    {A B : Thin2Cat.Obj C}
    (h : Con (Thin2Cat.Hom C A B))
  → Set _
FiniteCompressionOn Obs h =
  FiniteCompressionWitness (processFactorisation Obs h)

finiteCompression→opaqueFamily
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → FiniteCompressionWitness F
  → OpaqueFamily F
finiteCompression→opaqueFamily {O₂ = O₂} {Vpublic = Vpublic} fc =
  record
    { source = source fc
    ; i = i fc
    ; k = k fc
    ; distinct = distinct fc
    ; publicCollapsed =
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning O₂
          open R using (begin≈_; _≈⟨_⟩_; _∎≈)
        in
        begin≈
          μ Vpublic (at (family (source fc)) (i fc)) ≈⟨ ≈-sym {CP = O₂} (sound fc (i fc)) ⟩
          μ Vpublic (at T (assign fc (i fc))) ≈⟨ sameTarget≈ ⟩
          μ Vpublic (at T (assign fc (k fc))) ≈⟨ sound fc (k fc) ⟩
          μ Vpublic (at (family (source fc)) (k fc)) ∎≈
    }
  where
    T = family (target fc)
    sameTarget≡
      : at T (assign fc (i fc)) ≡ at T (assign fc (k fc))
    sameTarget≡ = cong (at T) (merged fc)

    sameTarget≈
      : _≈_ O₂ (μ Vpublic (at T (assign fc (i fc))))
                 (μ Vpublic (at T (assign fc (k fc))))
    sameTarget≈ = ≡→≈ {CP = O₂} (cong (μ Vpublic) sameTarget≡)

finiteCompression-obstructsPublicReadbackOn
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → (fc : FiniteCompressionWitness F)
  → ¬ PublicReadbackOn (family (source fc)) Vprivate Vpublic
finiteCompression-obstructsPublicReadbackOn fc =
  opaqueFamily-obstructsPublicReadbackOn (finiteCompression→opaqueFamily fc)

finiteCompression-obstructsFaithfulPublicObservationOn
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → (fc : FiniteCompressionWitness F)
  → ¬ FaithfulPublicObservationOn (family (source fc)) Vprivate Vpublic
finiteCompression-obstructsFaithfulPublicObservationOn fc =
  opaqueFamily-obstructsFaithfulPublicObservationOn (finiteCompression→opaqueFamily fc)

finiteLoss-count≤
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → (fc : FiniteCompressionWitness F)
  → size (family (target fc)) ≤ℕ size (family (source fc))
finiteLoss-count≤ fc =
  surjective⇒size≤ (assign fc) (surjective fc)

finiteLossGap
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → (fc : FiniteCompressionWitness F)
  → Σ ℕ
      (λ gap →
        ((size (family (target fc)) + gap) ≤ℕ size (family (source fc)))
        ×
        (size (family (source fc)) ≤ℕ (size (family (target fc)) + gap)))
finiteLossGap fc =
  ≤ℕ-gapWitness (finiteLoss-count≤ fc)
  where
    ≤ℕ-gapWitness
      : ∀ {m n}
      → m ≤ℕ n
      → Σ ℕ (λ gap → ((m + gap) ≤ℕ n) × (n ≤ℕ (m + gap)))
    ≤ℕ-gapWitness {zero} {n} _ =
      n , (≤ℕ-refl , ≤ℕ-refl)
    ≤ℕ-gapWitness {suc m} {suc n} (s≤s m≤n)
      with ≤ℕ-gapWitness {m} {n} m≤n
    ... | gap , (m+gap≤n , n≤m+gap) =
      gap , (s≤s m+gap≤n , s≤s n≤m+gap)

lossFrom≤
  : ∀ {m n}
  → m ≤ℕ n
  → ℕ
lossFrom≤ {zero} {n} _ = n
lossFrom≤ {suc m} {suc n} (s≤s m≤n) =
  lossFrom≤ m≤n

finiteLossCount
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → FiniteCompressionWitness F
  → ℕ
finiteLossCount fc =
  lossFrom≤ (finiteLoss-count≤ fc)

finiteLoss-strictGap
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → (fc : FiniteCompressionWitness F)
  → suc (size (family (target fc))) ≤ℕ size (family (source fc))
finiteLoss-strictGap fc =
  surjective+collision⇒suc-target≤source
    (assign fc)
    (surjective fc)
    ((i fc , k fc) , (distinct fc , merged fc))

finiteLossCount-atLeastOne
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {Vprivate : View X O₁}
    {Vpublic : View X O₂}
    {F : FactorisesThrough Vprivate Vpublic}
  → (fc : FiniteCompressionWitness F)
  → suc zero ≤ℕ finiteLossCount fc
finiteLossCount-atLeastOne fc =
  lossFrom≤-atLeastOne (finiteLoss-count≤ fc) (finiteLoss-strictGap fc)
  where
    lossFrom≤-atLeastOne
      : ∀ {m n}
      → (m≤n : m ≤ℕ n)
      → suc m ≤ℕ n
      → suc zero ≤ℕ lossFrom≤ m≤n
    lossFrom≤-atLeastOne {zero} {suc n} m≤n source+1≤gap =
      source+1≤gap
    lossFrom≤-atLeastOne {suc m} {suc n} (s≤s m≤n) (s≤s source+1≤gap) =
      lossFrom≤-atLeastOne m≤n source+1≤gap
