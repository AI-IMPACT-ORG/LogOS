{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.Dsl where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.API.Kernel

open import LogOS.API.Kernel.TensorDSL
open import LogOS.ZFC.SetTheory.Pack using (ZFAxioms)

-- Boundary-oriented DSL for ZF-style models.
-- Every instantiation first supplies a ZFAxioms pack, then records how its
-- sets inhabit the kernel boundary and how membership/equality interact with
-- the canonical tensor/endomap DSL endomap.

record ZFDsl {ℓ}
             {Sig : LogOSSignature ℓ}
             {Q   : QAdapter ℓ}
             (K   : Kernel Sig Q)
             : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  private
    module Bnd = ConPreorder (BulkBoundary.bnd BB)
  field
    axioms : ZFAxioms (kernelLike-fromKernel K)

  open ZFAxioms axioms public

  field
    realise      : SetU → Bnd.Con
    mem⇒flow     : ∀ {x y} → (x ∈ y)
                 → Bnd._⊑_ (realise x) (Endo.fn (Flow-Endo K) (realise y))
    eq⇒realise≡  : ∀ {x y} → x ≈ y → realise x ≡ realise y
    tf-stable    : ∀ x
                 → Bnd._⊑_ (Endo.fn (Flow-Endo K) (realise x)) (realise x)

  Flow-shadow : SetU → Bnd.Con
  Flow-shadow x = Endo.fn (Flow-Endo K) (realise x)

  mem-traces : ∀ {x y} → (x ∈ y) → Bnd._⊑_ (realise x) (Flow-shadow y)
  mem-traces = mem⇒flow

  Flow-contained : ∀ x → Bnd._⊑_ (Flow-shadow x) (realise x)
  Flow-contained = tf-stable

surfaceToZFAxioms
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ZFDsl K → ZFAxioms (kernelLike-fromKernel K)
surfaceToZFAxioms surf = ZFDsl.axioms surf
