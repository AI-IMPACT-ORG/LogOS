{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions.Diagonal where

open import LogOS.Prelude
open import Data.Product using (Σ; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Minimal.Con
open import LogOS.Theorems.Meta.Assumptions.Core using (Provability; ProvabilityOps)

-- Diagonalisation and self-reference packs.
--
-- These assumptions are intentionally separated from `Assumptions.Core` so that
-- imports make the trust boundary explicit.

record Diagonalization {ℓ}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K  : Kernel Sig Q)
                       (Pr : Provability K)
                       (Op : ProvabilityOps K)
                       : Set (lsuc ℓ) where
  open Kernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    diag : (Code → Code) → Code
    -- Internal fixed-point: ⊢ diag f ↔ f (diag f)
    diag→ : ∀ f → ⊢ (Imp (diag f) (f (diag f)))
    →diag : ∀ f → ⊢ (Imp (f (diag f)) (diag f))

-- A purely syntactic self-reference/representation pack for codes, kept outside the core.
-- It states that definable functions f : Code → Code are represented by single-hole
-- templates, and that each template admits a self-instantiation.
--
-- Two variants are provided:
-- - `QuoteSubst⊑`: aligned with the boundary preorder (mutual refinement).
-- - `QuoteSubst` : convenience variant aligned with decode-level equality.

record QuoteSubst⊑ {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  open Kernel K
  private
    _⊑_ = ConPoset._⊑_ (BulkBoundary.bnd BB)
  field
    Code₁         : Set ℓ
    inst          : Code₁ → Code → Code
    representable : (f : Code → Code) → Σ Code₁ (λ u → ∀ γ →
                      (decode (inst u γ) ⊑ decode (f γ))
                    × (decode (f γ) ⊑ decode (inst u γ)))
    self          : (u : Code₁) → Σ Code (λ s →
                      (decode s ⊑ decode (inst u s))
                    × (decode (inst u s) ⊑ decode s))

record QuoteSubst {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K   : Kernel Sig Q)
                  : Set (lsuc ℓ) where
  open Kernel K
  field
    Code₁         : Set ℓ
    inst          : Code₁ → Code → Code
    representable : (f : Code → Code) → Σ Code₁ (λ u → ∀ γ → decode (inst u γ) ≡ decode (f γ))
    self          : (u : Code₁) → Σ Code (λ s → decode s ≡ decode (inst u s))

-- A thin reflection principle: decode-equality implies provability of an implication
-- built with the object-level Imp constructor. This stays model-local.
--
-- Two variants are provided:
-- - `DecodeImp⊑`: from boundary entailment/refinement.
-- - `DecodeImp` : from decode-level equality.

record DecodeImp⊑ {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K  : Kernel Sig Q)
                  (Pr : Provability K)
                  (Op : ProvabilityOps K)
                  : Set (lsuc ℓ) where
  open Kernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  private
    _⊑_ = ConPoset._⊑_ (BulkBoundary.bnd BB)
  field
    from-decode⊑→imp : ∀ {φ ψ} → decode φ ⊑ decode ψ → ⊢ (Imp φ ψ)

record DecodeImp {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K  : Kernel Sig Q)
                 (Pr : Provability K)
                 (Op : ProvabilityOps K)
                 : Set (lsuc ℓ) where
  open Kernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    from-decode≡→imp : ∀ {φ ψ} → decode φ ≡ decode ψ → ⊢ (Imp φ ψ)

Diagonalization-from-QuoteSubst
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (QS : QuoteSubst K)
    (DI : DecodeImp K Pr Op)
  → Diagonalization K Pr Op
Diagonalization-from-QuoteSubst K Pr Op QS DI = record
  { diag  = diag
  ; diag→ = diag→
  ; →diag = →diag
  }
  where
    open Kernel K
    open Provability Pr renaming (Prov to ⊢)
    open ProvabilityOps Op
    open QuoteSubst QS
    open DecodeImp DI

    diag : (Code → Code) → Code
    diag f = s where
      rep : Σ Code₁ (λ u₁ → ∀ γ → decode (inst u₁ γ) ≡ decode (f γ))
      rep = representable f
      u : Code₁
      u = proj₁ rep
      repr : ∀ γ → decode (inst u γ) ≡ decode (f γ)
      repr = proj₂ rep
      se : Σ Code (λ s₁ → decode s₁ ≡ decode (inst u s₁))
      se = self u
      s : Code
      s = proj₁ se
      _ = proj₂ se -- decode s ≡ decode (inst u s)

    diag→ : ∀ f → ⊢ (Imp (diag f) (f (diag f)))
    diag→ f = from-decode≡→imp eq
      where
        rep : Σ Code₁ (λ u₁ → ∀ γ → decode (inst u₁ γ) ≡ decode (f γ))
        rep = representable f
        u : Code₁
        u = proj₁ rep
        repr : ∀ γ → decode (inst u γ) ≡ decode (f γ)
        repr = proj₂ rep
        se : Σ Code (λ s₁ → decode s₁ ≡ decode (inst u s₁))
        se = self u
        s : Code
        s = proj₁ se
        selfeq : decode s ≡ decode (inst u s)
        selfeq = proj₂ se
        eq : decode (diag f) ≡ decode (f (diag f))
        eq = trans selfeq (repr s)

    →diag : ∀ f → ⊢ (Imp (f (diag f)) (diag f))
    →diag f = from-decode≡→imp (sym eq)
      where
        rep : Σ Code₁ (λ u₁ → ∀ γ → decode (inst u₁ γ) ≡ decode (f γ))
        rep = representable f
        u : Code₁
        u = proj₁ rep
        repr : ∀ γ → decode (inst u γ) ≡ decode (f γ)
        repr = proj₂ rep
        se : Σ Code (λ s₁ → decode s₁ ≡ decode (inst u s₁))
        se = self u
        s : Code
        s = proj₁ se
        selfeq : decode s ≡ decode (inst u s)
        selfeq = proj₂ se
        eq : decode (diag f) ≡ decode (f (diag f))
        eq = trans selfeq (repr s)

open import LogOS.Computation.Core as CompCore
open import LogOS.Syntax.Prop using (_↔_; ¬_)

record HaltingModel {ℓ}
                    {Sig : LogOSSignature ℓ}
                    {Q   : QAdapter ℓ}
                    (K  : Kernel Sig Q)
                    : Set (lsuc ℓ) where
  open Kernel K
  field
    Comp : CompCore.Computation Code

record HaltingDiagonal {ℓ}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K  : Kernel Sig Q)
                       (HM : HaltingModel K)
                       : Set (lsuc ℓ) where
  open Kernel K
  open HaltingModel HM
  open CompCore.Computation Comp renaming (Halts to HaltsC)
  field
    -- Restricted diagonalisation (no-omniscience form): only against decidable P.
    liarForDecider
      : (P : Code → Set ℓ)
      → (decP : ∀ γ → P γ ⊎ ¬ P γ)
      → Σ Code (λ L → (HaltsC L) ↔ (¬ (P L)))

record TruthDiagonal {ℓ}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K  : Kernel Sig Q)
                     (TruthK : Kernel.Code K → Set ℓ)
                     : Set (lsuc ℓ) where
  open Kernel K
  field
    -- Restricted diagonalisation (no-omniscience form): only against decidable P.
    liarForDecider
      : (P : Code → Set ℓ)
      → (decP : ∀ γ → P γ ⊎ ¬ P γ)
      → Σ Code (λ γ → (TruthK γ) ↔ (¬ (P γ)))

-- Code-generic form:
-- this decouples diagonalisation from any particular kernel structure, so it
-- can be instantiated equally for `Kernel` and `GradedKernel` code languages.

record TruthDiagonalC {ℓCode ℓTruth : Level}
                      (Code   : Set ℓCode)
                      (TruthK : Code → Set ℓTruth)
                      : Set (lsuc (ℓCode ⊔ ℓTruth)) where
  field
    liarForDecider
      : (P : Code → Set ℓTruth)
      → (decP : ∀ γ → P γ ⊎ ¬ P γ)
      → Σ Code (λ γ → (TruthK γ) ↔ (¬ (P γ)))

TruthDiagonal→TruthDiagonalC
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {K   : Kernel Sig Q}
    (TruthK : Kernel.Code K → Set ℓ)
  → TruthDiagonal K TruthK
  → TruthDiagonalC (Kernel.Code K) TruthK
TruthDiagonal→TruthDiagonalC TruthK TD =
  record { liarForDecider = TruthDiagonal.liarForDecider TD }
