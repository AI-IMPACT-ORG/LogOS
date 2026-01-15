{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions.Core where

open import LogOS.Prelude
open import Data.Product using (Σ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Minimal.Con
open import LogOS.Theorems.Meta.Base using (NonTrivialC)
import LogOS.Theorems.Meta.ObserverCore as ObsCore

-- Shared assumption packs for conditional meta theorems.
--
-- This module is intentionally “structural”: it contains only the minimal packs
-- that do not themselves introduce diagonalisation/self-reference principles.

DecodeExtensional
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
-- `DecodeExtensional K P` is not an axiom about `decode` (and does not assume any
-- form of function extensionality). It is a *predicate-compatibility* condition:
-- `P` must be insensitive to code representation beyond decoded meaning.
DecodeExtensional K P =
  ObsCore.DecodeExtensional (Kernel.decode K) P

DecodeExtensionalFn
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    {X : Set ℓX}
    (f : Kernel.Code K → X)
  → Set (ℓ ⊔ ℓX)
-- Function-specialised variant: `f` respects decoded meaning.
DecodeExtensionalFn K f =
  ∀ γ₁ γ₂ → Kernel.decode K γ₁ ≡ Kernel.decode K γ₂ → f γ₁ ≡ f γ₂

-- Kernel-independent provability scaffolding (reused by Löb/Gödel core).

record ProvabilityOpsC {ℓCode : Level} (Code : Set ℓCode) : Set (lsuc ℓCode) where
  field
    Imp : Code → Code → Code
    Box : Code → Code

record ImpRulesC {ℓCode ℓPr : Level}
                 {Code : Set ℓCode}
                 (⊢    : Code → Set ℓPr)
                 (Op   : ProvabilityOpsC Code)
                 : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    mp   : ∀ {φ ψ} → ⊢ (Imp φ ψ) → ⊢ φ → ⊢ ψ
    impI : ∀ {φ ψ} → (⊢ φ → ⊢ ψ) → ⊢ (Imp φ ψ)

record HBLClassicC {ℓCode ℓPr : Level}
                   {Code : Set ℓCode}
                   (⊢    : Code → Set ℓPr)
                   (Op   : ProvabilityOpsC Code)
                   : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    Necessitation : ∀ φ → ⊢ φ → ⊢ (Box φ)
    Kdist         : ∀ φ ψ → ⊢ (Box (Imp φ ψ)) → (⊢ (Box φ) → ⊢ (Box ψ))
    Four          : ∀ φ → ⊢ (Box φ) → ⊢ (Box (Box φ))

record BoundaryFix {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q : QAdapter ℓ}
                   (K : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  open Kernel K
  private
    CP   = BulkBoundary.bnd BB
    Con∂ = ConPoset.Con CP
    _⊑_  = ConPoset._⊑_ CP

  -- Textbook side-condition for fixed-point theorems (Knaster–Tarski / Scott).
  Mono : (Con∂ → Con∂) → Set ℓ
  Mono f = MonoOn CP f

  -- A boundary fixed-point principle (up to the preorder): every monotone endomap
  -- has a fixed point, witnessed as mutual refinement.
  field
    fixH : (f : Con∂ → Con∂) → Mono f → Σ Con∂ (λ c → (c ⊑ f c) × (f c ⊑ c))

record Provability {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q : QAdapter ℓ}
                   (K : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    Prov    : Kernel.Code K → Set ℓ
    ext     : DecodeExtensional K Prov
    nontriv : NonTrivialC {K = K} Prov

record ProvabilityOps {ℓ}
                      {Sig : LogOSSignature ℓ}
                      {Q : QAdapter ℓ}
                      (K : Kernel Sig Q)
                      : Set (lsuc ℓ) where
  open Kernel K
  field
    Imp : Code → Code → Code
    Box : Code → Code

toOpsC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ProvabilityOps K
  → ProvabilityOpsC (Kernel.Code K)
toOpsC Op = record
  { Imp = ProvabilityOps.Imp Op
  ; Box = ProvabilityOps.Box Op
  }

-- Minimal implicational fragment over the model-provided `Imp` constructor.
-- We keep this separate so metatheorems can precisely state when they need
-- “plain” propositional reasoning in addition to provability-side axioms.

record ImpRules {ℓ}
                {Sig : LogOSSignature ℓ}
                {Q : QAdapter ℓ}
                (K  : Kernel Sig Q)
                (Pr : Provability K)
                (Op : ProvabilityOps K)
                : Set (lsuc ℓ) where
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    mp   : ∀ {φ ψ} → ⊢ (Imp φ ψ) → ⊢ φ → ⊢ ψ
    impI : ∀ {φ ψ} → (⊢ φ → ⊢ ψ) → ⊢ (Imp φ ψ)

toImpRulesC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K  : Kernel Sig Q}
    {Pr : Provability K}
    {Op : ProvabilityOps K}
  → ImpRules K Pr Op
  → ImpRulesC (Provability.Prov Pr) (toOpsC Op)
toImpRulesC Ir = record
  { mp   = ImpRules.mp Ir
  ; impI = ImpRules.impI Ir
  }

-- HBL (classic):
-- 1) Necessitation: if ⊢ φ then ⊢ Box φ
-- 2) Distribution (K): ⊢ Box(φ → ψ) → (Box φ → Box ψ)
-- 3) 4-axiom: ⊢ Box φ → Box Box φ

record HBLClassic {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K  : Kernel Sig Q)
                  (Pr : Provability K)
                  (Op : ProvabilityOps K)
                  : Set (lsuc ℓ) where
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    Necessitation : ∀ φ → ⊢ φ → ⊢ (Box φ)
    Kdist         : ∀ φ ψ → ⊢ (Box (Imp φ ψ)) → (⊢ (Box φ) → ⊢ (Box ψ))
    Four          : ∀ φ → ⊢ (Box φ) → ⊢ (Box (Box φ))

toHBLClassicC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K  : Kernel Sig Q}
    {Pr : Provability K}
    {Op : ProvabilityOps K}
  → HBLClassic K Pr Op
  → HBLClassicC (Provability.Prov Pr) (toOpsC Op)
toHBLClassicC Hb = record
  { Necessitation = HBLClassic.Necessitation Hb
  ; Kdist         = HBLClassic.Kdist Hb
  ; Four          = HBLClassic.Four Hb
  }
