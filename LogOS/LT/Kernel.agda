{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Kernel where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _×CP_)
open import LogOS.LT.View using (View; μ; PullbackPreorder; DecodeView; mkRoleView; forget)

-- Kernel observation shape (design-target spec).
-- - boundary constraints `bnd(K)` as a constrained preorder
-- - a code type `Code(K)`
-- - an evaluator/decoder `decode : Code(K) → bnd(K)`
--
-- Encode is optional (a port) and factored out as `EncodePort`.
--
-- Code order is not primitive: it is induced by decoding (pullback preorder).

record Kernel (ℓ ℓRel ℓCode : Level) : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where
  field
    bnd    : ConPreorder ℓ ℓRel
    Code   : Set ℓCode
    decode : Code → Con bnd

open Kernel public
-- Kernel from a canonical view into its boundary.
--
-- This makes the “decode-first” discipline explicit: a kernel is (at minimum)
-- a boundary interface together with a chosen observation map into it.
kernelFromView
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
  → View X O
  → Kernel ℓOCon ℓORel ℓX
kernelFromView {X = X} {O = O} V =
  record
    { bnd = O
    ; Code = X
    ; decode = μ V
    }

-- Canonical view of code into the boundary (the observation interface).
decodeView : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) → DecodeView (Code K) (bnd K)
decodeView K = mkRoleView (record { μ = decode K })

-- Optional boundary → code interface (synthesis/compilation port).
record EncodePort {ℓ ℓRel ℓCode : Level} (K : Kernel ℓ ℓRel ℓCode) : Set (lsuc (ℓ ⊔ ℓCode)) where
  field
    encode : Con (bnd K) → Code K

open EncodePort public
-- Boundary-as-code kernel: treat any boundary preorder as a kernel whose code
-- *is* boundary constraints and whose decode is identity.
BoundaryKernel
  : ∀ {ℓCon ℓRel : Level}
  → ConPreorder ℓCon ℓRel
  → Kernel ℓCon ℓRel ℓCon
BoundaryKernel CP =
  record
    { bnd = CP
    ; Code = Con CP
    ; decode = λ c → c
    }

-- The induced code preorder: pull back boundary refinement along `decode`.
CodePreorder : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) → ConPreorder ℓCode ℓRel
CodePreorder K = PullbackPreorder (forget (decodeView K))

ObservedCodePreorder : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) → ConPreorder ℓCode ℓRel
ObservedCodePreorder = CodePreorder

-- Product kernel (componentwise boundary and code).
Kernel×
  : ∀ {ℓCon₁ ℓRel₁ ℓCode₁ ℓCon₂ ℓRel₂ ℓCode₂ : Level}
  → Kernel ℓCon₁ ℓRel₁ ℓCode₁
  → Kernel ℓCon₂ ℓRel₂ ℓCode₂
  → Kernel (ℓCon₁ ⊔ ℓCon₂) (ℓRel₁ ⊔ ℓRel₂) (ℓCode₁ ⊔ ℓCode₂)
Kernel× K₁ K₂ =
  record
    { bnd = bnd K₁ ×CP bnd K₂
    ; Code = Code K₁ × Code K₂
    ; decode = λ (γ₁ , γ₂) → (decode K₁ γ₁ , decode K₂ γ₂)
    }
