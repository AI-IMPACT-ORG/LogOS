{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.InterlinguaKernelLayer where

-- Generic kernel-layer interlingua:
-- a kernel layer with its satisfaction relation translates canonically into
-- any boundary port via a SatMor, uniquely up to boundary satisfaction.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

open import LogOS.Kernel
import LogOS.Boundary.FromKernel as KBoundary

open import LogOS.Ports.Semantic.HeteroInterlinguaCore using (PresentationC; canonicalPresentation)
open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.PresentationCore using (satSystem)
open import LogOS.Ports.Semantic.Core using (boundarySatSystemFromIO)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm : Level}
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  {ℓX ℓSat : Level}
  (X : Set ℓX)
  (SatX : LogOSSignature.Cosp Sig → X → Set ℓSat)
  (m0 : SatMor
          (satSystem (LogOSSignature.Cosp Sig) X SatX)
          (boundarySatSystemFromIO (KBoundary.boundaryIO K)))
  where

  B : BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  B = KBoundary.boundaryIO K

  m : SatMor
        (satSystem (LogOSSignature.Cosp Sig) X SatX)
        (boundarySatSystemFromIO B)
  m = m0

  P₁ : PresentationC (satSystem (LogOSSignature.Cosp Sig) X SatX)
  P₁ = canonicalPresentation (satSystem (LogOSSignature.Cosp Sig) X SatX)

  P₂ : PresentationC (boundarySatSystemFromIO B)
  P₂ = toPresentationC B P

  module H = Hetero.For m P₁ P₂

  open H public using (SemPreserving; _≈⇒_; SatF₂↑)

  compile : X → BoundaryPort.Form P
  compile = H.translate

  compile-preserves-Sat
    : ∀ (w : LogOSSignature.Cosp Sig) (x : X)
    → Prop._↔_
        (SatX w x)
        (H.SatF₂↑ w (compile x))
  compile-preserves-Sat = H.translate-preserves-Sat

  compile-unique
    : ∀ (t : X → BoundaryPort.Form P)
    → H.SemPreserving t
    → H._≈⇒_ t compile
  compile-unique = H.translate-unique

  -- Any `SemPreserving` interpretation is observationally equivalent
  -- to the canonical compiler.
  compile≈interp
    : ∀ (t : X → BoundaryPort.Form P)
    → H.SemPreserving t
    → H._≈⇒_ compile t
  compile≈interp t pres =
    let eq = H.translate-unique t pres in
    (H.Trans≈⇐ eq , H.Trans≈⇒ eq)
