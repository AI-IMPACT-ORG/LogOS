{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.SetTheory.FullUpgradeFromDefinable where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import LogOS.Domain.SetTheory.DefinablePack using (ZFAxiomsᵈ)
open import LogOS.Domain.SetTheory.Pack using (ZFAxioms)

-- “Full ZF” differs from `ZFAxiomsᵈ` exactly at the schemata:
--   Separation  : quantify over *all* predicates `SetU → Set`
--   Replacement : quantify over *all* (Agda-level) functions `SetU → SetU`
--
-- LogOS-native way to express the gap: require *representability by codes*.
--
--  * A predicate is representable if it is the membership predicate of some `⟦ γ ⟧`.
--  * A function is representable if its graph is definable by some code `γ` via `Graph γ`.
--
-- Remark: if you instead take “full Separation/Replacement” to mean “for every
-- *formula* in the object language”, then one can stay in the coded world and
-- avoid these meta-level representability assumptions entirely (Metamath-style).

record PredicateRepresentable
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {K : Kernel Sig Q}
  (A : ZFAxiomsᵈ K)
  : Set (lsuc (lsuc ℓ)) where
  open ZFAxiomsᵈ A
  field
    represent
      : (P : SetU → Set ℓ)
      → Σ (Kernel.Code K) (λ γ → ∀ z → (z ∈ ⟦ γ ⟧) ↔ P z)

record FunctionGraphRepresentable
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {K : Kernel Sig Q}
  (A : ZFAxiomsᵈ K)
  : Set (lsuc (lsuc ℓ)) where
  open ZFAxiomsᵈ A
  field
    represent
      : (F : SetU → Σ SetU (λ _ → Set ℓ))
      → Σ (Kernel.Code K)
          (λ γ → ∀ u z → Graph γ u z ↔ (proj₁ (F u) ≈ z))

module Upgrade
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {K : Kernel Sig Q}
  (A : ZFAxiomsᵈ K)
  (PR : PredicateRepresentable A)
  (FR : FunctionGraphRepresentable A)
  where

  open ZFAxiomsᵈ A
  private
    repPred = PredicateRepresentable.represent PR
    repFun  = FunctionGraphRepresentable.represent FR

  separation-full
    : (P : SetU → Set ℓ)
    → ∀ x → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × (P z)))
  separation-full P x =
    let rep = repPred P
        γ = proj₁ rep
        spec = proj₂ rep
        ypack = separationᵈ γ x
        y = proj₁ ypack
        memy = proj₂ ypack
    in
    y , (λ z →
      intro
        (λ z∈y →
          let (z∈x , z∈γ) = _↔_.to (memy z) z∈y
          in (z∈x , _↔_.to (spec z) z∈γ))
        (λ { (z∈x , Pz) →
          _↔_.from (memy z) (z∈x , _↔_.from (spec z) Pz) }))

  replacement-full
    : (F : SetU → Σ SetU (λ _ → Set ℓ))
    → ∀ x →
      Σ SetU
        (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → u ∈ x × (proj₁ (F u) ≈ z))))
  replacement-full F x =
    let rep = repFun F
        γ = proj₁ rep
        spec = proj₂ rep
        funGraph = λ u z₁ z₂ g₁ g₂ →
          trans≈
            (sym≈ (_↔_.to (spec u z₁) g₁))
            (_↔_.to (spec u z₂) g₂)
        ypack = replacementᵈ γ funGraph x
        y = proj₁ ypack
        memy = proj₂ ypack
    in
    y , (λ z →
      intro
        (λ z∈y →
          let (u , (ux , gz)) = _↔_.to (memy z) z∈y
          in u , (ux , _↔_.to (spec u z) gz))
        (λ { (u , (ux , Fu≈z)) →
          _↔_.from (memy z) (u , (ux , _↔_.from (spec u z) Fu≈z)) }))

  ZF : ZFAxioms K
  ZF = record
    { SetU   = SetU
    ; _∈_    = _∈_
    ; _≈_    = _≈_
    ; refl≈  = refl≈
    ; sym≈   = sym≈
    ; trans≈ = trans≈
    ; ⟦_⟧     = ⟦_⟧
    ; by-decode≈ = by-decode≈
    ; extensionality = extensionality
    ; mem-ext = mem-ext
    ; empty = empty
    ; pairing = pairing
    ; union = union
    ; powerset = powerset
    ; zeroS = zeroS
    ; zeroS-empty = zeroS-empty
    ; succ  = succ
    ; mem-succ↔ = mem-succ↔
    ; infinity = infinity
    ; separation = separation-full
    ; replacement = replacement-full
    ; foundation = foundation
    }
