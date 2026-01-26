{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.KernelCat where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Initial
open import LogOS.Minimal.World
open import LogOS.Theorems.Meta.DecodeTransportKit using (decode-mapCode-cong)

-- Category of Kernels for fixed Sig, Q, with hom-equality up to strict decode equality (`≡`).

record KernelCat {ℓ}
                 (Sig : LogOSSignature ℓ)
                 (Q   : QAdapter ℓ)
                 : Set (lsuc (lsuc (lsuc ℓ))) where
  infixr 9 _∘_
  field
    Hom   : (A B : Kernel Sig Q) → Set (lsuc (lsuc ℓ))
    _∘_   : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id    : ∀ {A} → Hom A A
    -- Equality up to strict decode equality (`≡`) on code maps at the target kernel
    eqHom : ∀ {A B} → Hom A B → Hom A B → Set ℓ
    reflH : ∀ {A B} {h : Hom A B} → eqHom h h
    symH  : ∀ {A B} {h k : Hom A B} → eqHom h k → eqHom k h
    transH : ∀ {A B} {h k l : Hom A B} → eqHom h k → eqHom k l → eqHom h l
    congL : ∀ {A B C} {h₁ h₂ : Hom A B} (g : Hom B C) → eqHom h₁ h₂ → eqHom (g ∘ h₁) (g ∘ h₂)
    congR : ∀ {A B C} {h₁ h₂ : Hom B C} (g : Hom A B) → eqHom h₁ h₂ → eqHom (h₁ ∘ g) (h₂ ∘ g)

-- Concrete instance for kernels

KernelCat-instance
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  → KernelCat Sig Q
KernelCat-instance Sig Q = record
  { Hom   = KernelHom
  ; _∘_   = λ {A} {B} {C} g f → composeKernelHom f g
  ; id    = λ {A} → idKernelHom A
  ; eqHom = λ {A} {B} h k → ∀ γ → Kernel.decode B (KernelHom.mapCode h γ) ≡ Kernel.decode B (KernelHom.mapCode k γ)
  ; reflH = λ γ → refl
  ; symH  = λ e γ → sym (e γ)
  ; transH = λ e₁ e₂ γ → trans (e₁ γ) (e₂ γ)
  ; congL = λ {A} {B} {C} {h₁} {h₂} g e γ →
              decode-mapCode-cong g (e γ)
  ; congR = λ {A} {B} {C} {h₁} {h₂} g e γ → e (KernelHom.mapCode g γ)
  }

-- Laws for the concrete kernel category instance.
--
-- These are definitional for `KernelCat-instance` (composition/identity are
-- implemented by record-level function composition on `mapCode`), but packaging
-- them here avoids repeating ad-hoc “composeKernelHom/idKernelHom” lemmas in
-- downstream category-theoretic developments.

module Laws {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  private
    C : KernelCat Sig Q
    C = KernelCat-instance Sig Q

  open KernelCat C

  idL : ∀ {A B : Kernel Sig Q} (f : Hom A B) → eqHom (id ∘ f) f
  idL f γ = refl

  idR : ∀ {A B : Kernel Sig Q} (f : Hom A B) → eqHom (f ∘ id) f
  idR f γ = refl

  assoc
    : ∀ {A B C D : Kernel Sig Q}
      (h : Hom C D) (g : Hom B C) (f : Hom A B)
    → eqHom ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
  assoc h g f γ = refl

-- Initiality up to strict decode equality (`≡`) packaged as a theorem from InitialKernel

record InitialUpToDecode {ℓ}
                         (Sig : LogOSSignature ℓ)
                         (Q   : QAdapter ℓ)
                         : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    C     : KernelCat Sig Q
    I     : Kernel Sig Q
    fold  : ∀ (K : Kernel Sig Q) → KernelCat.Hom C I K
    init  : ∀ (K : Kernel Sig Q) (h : KernelCat.Hom C I K)
            → KernelCat.eqHom C (fold K) h

initial-from-build
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (H : (let module W = Worlds Sig in W.WorldH Q))
  → InitialUpToDecode Sig Q
initial-from-build Sig Q H = record
  { C    = KernelCat-instance Sig Q
  ; I    = InitialKernel.FreeK IK
  ; fold = InitialKernel.foldK IK
  ; init = λ K h γ →
            -- Use unique≃ from InitialKernel
            let _ , _ , eqγ = InitialKernel.unique≃ IK K h in eqγ γ
  }
  where
    IK = build Sig Q H
