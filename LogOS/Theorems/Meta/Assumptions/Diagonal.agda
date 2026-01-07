{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions.Diagonal where

open import LogOS.Prelude
open import Data.Product using (Σ; proj₁; proj₂; fst; snd)

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

-- ----------------------------------------------------------------------------
-- Lawvere fixed point (boundary-preorder form).
--
-- In the presence of `QuoteSubst⊑ K` (a “code-as-internal-hom” witness), we can
-- produce a decoded fixed point of any endomap `f : Code → Code` without
-- assuming antisymmetry of the boundary preorder.

InternalHomWitness
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Set (lsuc ℓ)
InternalHomWitness = QuoteSubst⊑

lawvereFix
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → InternalHomWitness K
  → (f : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ s →
      ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Kernel.decode K s) (Kernel.decode K (f s))
      ×
      ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Kernel.decode K (f s)) (Kernel.decode K s))
lawvereFix {K = K} QS f =
  let
    open Kernel K
    open QuoteSubst⊑ QS

    rep  = representable f
    u    = proj₁ rep
    repr = proj₂ rep
    se   = self u
    s    = proj₁ se

    selfL = fst (proj₂ se)
    selfR = snd (proj₂ se)
    reprL = fst (repr s)
    reprR = snd (repr s)

    left  = ConPoset.trans (BulkBoundary.bnd BB) selfL reprL
    right = ConPoset.trans (BulkBoundary.bnd BB) reprR selfR
  in
  s , (left , right)

-- Optional strengthening: if the boundary preorder is antisymmetric (a partial
-- order), the mutual refinement from `lawvereFix` upgrades to an equality.

lawvereFix≡
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → BulkBoundaryPO (Kernel.BB K)
  → InternalHomWitness K
  → (f : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ s → Kernel.decode K s ≡ Kernel.decode K (f s))
lawvereFix≡ {K = K} po QS f =
  let
    open Kernel K
    open BulkBoundaryPO po using (po-bnd)
    open PartialOrder po-bnd using (antisym)
    s , (le₁ , le₂) = lawvereFix {K = K} QS f
  in
  s , antisym le₁ le₂

-- A convenient fixed-point chooser (used by derived diagonalisation constructors).

lawvereDiag
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → InternalHomWitness K
  → (Kernel.Code K → Kernel.Code K)
  → Kernel.Code K
lawvereDiag QS f = proj₁ (lawvereFix QS f)

lawvereDiag≡
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → BulkBoundaryPO (Kernel.BB K)
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → Kernel.decode K (lawvereDiag QS f) ≡ Kernel.decode K (f (lawvereDiag QS f))
lawvereDiag≡ po QS f = proj₂ (lawvereFix≡ po QS f)

lawvereDiag-⊑
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (lawvereDiag QS f))
      (Kernel.decode K (f (lawvereDiag QS f)))
lawvereDiag-⊑ QS f = fst (proj₂ (lawvereFix QS f))

⊑-lawvereDiag
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (f (lawvereDiag QS f)))
      (Kernel.decode K (lawvereDiag QS f))
⊑-lawvereDiag QS f = snd (proj₂ (lawvereFix QS f))

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

-- Provability-level diagonalization as a theorem:
-- internal-hom witness + local decode⊑→imp bridge ⇒ the classical diagonal schema.

Diagonalization-from-InternalHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (IH : InternalHomWitness K)
    (DI : DecodeImp⊑ K Pr Op)
  → Diagonalization K Pr Op
Diagonalization-from-InternalHom K Pr Op IH DI = record
  { diag  = λ f → lawvereDiag IH f
  ; diag→ = λ f → DecodeImp⊑.from-decode⊑→imp DI (lawvereDiag-⊑ IH f)
  ; →diag = λ f → DecodeImp⊑.from-decode⊑→imp DI (⊑-lawvereDiag IH f)
  }

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
