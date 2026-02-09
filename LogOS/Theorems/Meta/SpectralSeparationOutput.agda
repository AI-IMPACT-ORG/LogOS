{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.SpectralSeparationOutput where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ¬_; ⊥; ⊥-elim; to)
open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.RelPreorder as RP using (EqRelPreorder)
open import LogOS.Minimal.View using (View; _≃[_]_; _≈[_]_; ConPreorder→RelPreorder)
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Assumptions.Diagonal using
  (TruthDiagonal; TruthDiagonalC; TruthDiagonal→TruthDiagonalC; liar-witnessC; no-totalC; liar-witness; no-total)
open import LogOS.Theorems.Meta.ConditionalPacks using (DecodeExtensionalFn≈)

-- A partial “spectral separation output” surface: for each code, either produce
-- some witness W (inj₁ w) or explicitly leave the input undefined (inj₂ tt).
-- This packages the intended epistemology: finite observers can certify some
-- separation facts, but not uniformly for all codes.

module Generic {ℓCode ℓDec : Level} (Code : Set ℓCode) (Dec : Set ℓDec) (decode : Code → Dec) where

  private
    decodeView : View Code (EqRelPreorder Dec)
    decodeView = record { μ = decode }

  record SpectralSeparationOutputC : Set (lsuc (ℓCode ⊔ ℓDec)) where
    field
      Witness : Set ℓCode
      infer   : Code → Witness ⊎ ⊤ {ℓ = lzero}
      ext     : ∀ γ₁ γ₂ → γ₁ ≃[ decodeView ] γ₂ → infer γ₁ ≡ infer γ₂

    HasSeparation : Code → Set ℓCode
    HasSeparation γ = Σ Witness (λ w → infer γ ≡ inj₁ w)

    NoSeparation : Code → Set ℓCode
    NoSeparation γ = infer γ ≡ inj₂ ttℓ

    ¬HasSeparation→NoSeparation : ∀ {γ} → ¬ HasSeparation γ → NoSeparation γ
    ¬HasSeparation→NoSeparation {γ} nh with infer γ
    ... | inj₂ ttℓ = refl
    ... | inj₁ w  = ⊥-elim (nh (w , refl))

  record SeparationTotalityClaimC (SSO : SpectralSeparationOutputC) : Set (lsuc ℓCode) where
    open SpectralSeparationOutputC SSO
    field
      Totality : Set ℓCode
      reflect  : Totality → ∀ γ → HasSeparation γ

  separation-output-not-totalC
    : (SSO : SpectralSeparationOutputC)
      (TD  : TruthDiagonalC Code (SpectralSeparationOutputC.HasSeparation SSO))
    → ¬ (∀ γ → SpectralSeparationOutputC.HasSeparation SSO γ)
  separation-output-not-totalC SSO TD = no-totalC TD

  separation-output-no-self-certificationC
    : (SSO : SpectralSeparationOutputC)
      (TD  : TruthDiagonalC Code (SpectralSeparationOutputC.HasSeparation SSO))
      (TC  : SeparationTotalityClaimC SSO)
    → SeparationTotalityClaimC.Totality TC → ⊥
  separation-output-no-self-certificationC SSO TD TC t =
    separation-output-not-totalC SSO TD (SeparationTotalityClaimC.reflect TC t)

  separation-output-diagonal-witnessC
    : (SSO : SpectralSeparationOutputC)
      (TD  : TruthDiagonalC Code (SpectralSeparationOutputC.HasSeparation SSO))
    → Σ Code (λ γ → SpectralSeparationOutputC.NoSeparation SSO γ)
  separation-output-diagonal-witnessC SSO TD =
    let
      open SpectralSeparationOutputC SSO
      w  = liar-witnessC TD
      γ  = proj₁ w
      nh = proj₂ w
    in
    (γ , ¬HasSeparation→NoSeparation nh)

module Generic≈ {ℓCode ℓDec : Level}
               (Code : Set ℓCode)
               (CP : ConPreorder ℓDec)
               (decode : Code → ConPreorder.Con CP)
               where

  private
    decodeView : View Code (ConPreorder→RelPreorder CP)
    decodeView = record { μ = decode }

  record SpectralSeparationOutputC : Set (lsuc (ℓCode ⊔ ℓDec)) where
    field
      Witness : Set ℓCode
      infer   : Code → Witness ⊎ ⊤ {ℓ = lzero}
      ext     : ∀ γ₁ γ₂ → γ₁ ≈[ decodeView ] γ₂ → infer γ₁ ≡ infer γ₂

    HasSeparation : Code → Set ℓCode
    HasSeparation γ = Σ Witness (λ w → infer γ ≡ inj₁ w)

    NoSeparation : Code → Set ℓCode
    NoSeparation γ = infer γ ≡ inj₂ ttℓ

    ¬HasSeparation→NoSeparation : ∀ {γ} → ¬ HasSeparation γ → NoSeparation γ
    ¬HasSeparation→NoSeparation {γ} nh with infer γ
    ... | inj₂ ttℓ = refl
    ... | inj₁ w  = ⊥-elim (nh (w , refl))

  record SeparationTotalityClaimC (SSO : SpectralSeparationOutputC) : Set (lsuc ℓCode) where
    open SpectralSeparationOutputC SSO
    field
      Totality : Set ℓCode
      reflect  : Totality → ∀ γ → HasSeparation γ

  separation-output-not-totalC
    : (SSO : SpectralSeparationOutputC)
      (TD  : TruthDiagonalC Code (SpectralSeparationOutputC.HasSeparation SSO))
    → ¬ (∀ γ → SpectralSeparationOutputC.HasSeparation SSO γ)
  separation-output-not-totalC SSO TD = no-totalC TD

  separation-output-no-self-certificationC
    : (SSO : SpectralSeparationOutputC)
      (TD  : TruthDiagonalC Code (SpectralSeparationOutputC.HasSeparation SSO))
      (TC  : SeparationTotalityClaimC SSO)
    → SeparationTotalityClaimC.Totality TC → ⊥
  separation-output-no-self-certificationC SSO TD TC t =
    separation-output-not-totalC SSO TD (SeparationTotalityClaimC.reflect TC t)

  separation-output-diagonal-witnessC
    : (SSO : SpectralSeparationOutputC)
      (TD  : TruthDiagonalC Code (SpectralSeparationOutputC.HasSeparation SSO))
    → Σ Code (λ γ → SpectralSeparationOutputC.NoSeparation SSO γ)
  separation-output-diagonal-witnessC SSO TD =
    let
      open SpectralSeparationOutputC SSO
      w  = liar-witnessC TD
      γ  = proj₁ w
      nh = proj₂ w
    in
    (γ , ¬HasSeparation→NoSeparation nh)

record SpectralSeparationOutput {ℓ}
                               {Sig : LogOSSignature ℓ}
                               {Q   : QAdapter ℓ}
                               (K   : Kernel Sig Q)
                               : Set (lsuc ℓ) where
  private
    module G = Generic≈ (Kernel.Code K) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.decode K)
  field
    core : G.SpectralSeparationOutputC

  open G.SpectralSeparationOutputC core public

-- A lightweight “oracle core” for spectral separation: fix the witness type and
-- expose `infer/ext` plus the induced `SpectralSeparationOutput`.

record Oracle {ℓ}
              {Sig : LogOSSignature ℓ}
              {Q   : QAdapter ℓ}
              (K   : Kernel Sig Q)
              (Witness : Set ℓ)
              : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  field
    -- `inj₁ w` returns a witness, `inj₂ tt` abstains (no output).
    infer : Code → Witness ⊎ ⊤ {ℓ = lzero}
    ext   : DecodeExtensionalFn≈ K infer

  toSSO : SpectralSeparationOutput K
  toSSO = record
    { core = record
        { Witness = Witness
        ; infer   = infer
        ; ext     = ext
        }
    }

-- A lightweight reflection surface: the theory can *name* a certificate of
-- totality and reflect it outward to a meta-level “defined everywhere” claim.

record SeparationTotalityClaim {ℓ}
                              {Sig : LogOSSignature ℓ}
                              {Q   : QAdapter ℓ}
                              {K   : Kernel Sig Q}
                              (SSO : SpectralSeparationOutput K)
                              : Set (lsuc ℓ) where
  private
    module G = Generic≈ (Kernel.Code K) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.decode K)
  field
    core : G.SeparationTotalityClaimC (SpectralSeparationOutput.core SSO)

  open G.SeparationTotalityClaimC core public

-- ============================================================================
-- General budget interface (graded/prequantale friendly)
--
-- This variant does not build a filtered `infer≤` (which would require a
-- decidable order on budgets). Instead it states “totality-within-budget” as a
-- predicate and diagonalizes against it.
-- ============================================================================

module GeneralB
  {ℓ}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {K   : Kernel Sig Q}
  (O   : SpectralSeparationOutput K)
  where

  open Kernel K
  open SpectralSeparationOutput O

  record WitnessCostB (B : Set ℓ) : Set (lsuc ℓ) where
    field
      costB : Witness → B

  module General
    (B : Set ℓ)
    (_≤B_ : B → B → Set ℓ)
    (CB : WitnessCostB B)
    where

    open WitnessCostB CB using (costB)

    WithinBudget
      : (Bnd : Code → B)
      → Code → Set ℓ
    WithinBudget Bnd γ =
      Σ Witness (λ w → infer γ ≡ inj₁ w × costB w ≤B Bnd γ)

    no-total-within-budget
      : ∀ (Bnd : Code → B)
        → TruthDiagonalC Code (WithinBudget Bnd)
        → ¬ (∀ γ → WithinBudget Bnd γ)
    no-total-within-budget Bnd TD = no-totalC TD

    no-total-within-budgetK
      : ∀ (Bnd : Code → B)
        → TruthDiagonal K (WithinBudget Bnd)
        → ¬ (∀ γ → WithinBudget Bnd γ)
    no-total-within-budgetK Bnd TD = no-total TD

    diagonal-witness-within-budget
      : ∀ (Bnd : Code → B)
        → TruthDiagonalC Code (WithinBudget Bnd)
        → Σ Code (λ γ → ¬ WithinBudget Bnd γ)
    diagonal-witness-within-budget Bnd TD = liar-witnessC TD

    diagonal-witness-within-budgetK
      : ∀ (Bnd : Code → B)
        → TruthDiagonal K (WithinBudget Bnd)
        → Σ Code (λ γ → ¬ WithinBudget Bnd γ)
    diagonal-witness-within-budgetK Bnd TD = liar-witness TD

-- Anti-totality: with a diagonal-against-decidable-observers principle for
-- HasSeparation, there cannot be a total separation output.

separation-output-not-total
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (SSO : SpectralSeparationOutput K)
    (TD  : TruthDiagonal K (SpectralSeparationOutput.HasSeparation SSO))
  → ¬ (∀ γ → SpectralSeparationOutput.HasSeparation SSO γ)
separation-output-not-total {K = K} SSO TD all =
  let module G = Generic≈ (Kernel.Code K) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.decode K)
  in G.separation-output-not-totalC (SpectralSeparationOutput.core SSO)
       (TruthDiagonal→TruthDiagonalC (SpectralSeparationOutput.HasSeparation SSO) TD)
       all

-- Meta-meta barrier: even “self-certified totality” collapses under diagonalization.

separation-output-no-self-certification
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (SSO : SpectralSeparationOutput K)
    (TD  : TruthDiagonal K (SpectralSeparationOutput.HasSeparation SSO))
    (TC  : SeparationTotalityClaim SSO)
  → SeparationTotalityClaim.Totality TC → ⊥
separation-output-no-self-certification SSO TD TC t =
  separation-output-not-total SSO TD (SeparationTotalityClaim.reflect TC t)

-- Consequence: diagonalization forces an explicit code into the undefined branch.

separation-output-diagonal-witness
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (SSO : SpectralSeparationOutput K)
    (TD  : TruthDiagonal K (SpectralSeparationOutput.HasSeparation SSO))
  → Σ (Kernel.Code K) (λ γ → SpectralSeparationOutput.NoSeparation SSO γ)
separation-output-diagonal-witness {K = K} SSO TD =
  let module G = Generic≈ (Kernel.Code K) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.decode K)
  in G.separation-output-diagonal-witnessC (SpectralSeparationOutput.core SSO)
       (TruthDiagonal→TruthDiagonalC (SpectralSeparationOutput.HasSeparation SSO) TD)
