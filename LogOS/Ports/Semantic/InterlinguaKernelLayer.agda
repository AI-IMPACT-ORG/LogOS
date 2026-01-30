{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
import LogOS.Kernel.Boundary as KBoundary

open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC; canonicalPresentation)
open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
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
  (m0 : SatMor (LogOSSignature.Cosp Sig) X SatX
               (LogOSSignature.∂Cosp Sig)
               (BulkBoundary.Con_bnd (Kernel.BB K))
               (BoundaryIO.Sat∂ (KBoundary.boundaryIO K)))
  where

  B : BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  B = KBoundary.boundaryIO K

  m : SatMor (LogOSSignature.Cosp Sig) X SatX
             (LogOSSignature.∂Cosp Sig)
             (BulkBoundary.Con_bnd (Kernel.BB K))
             (BoundaryIO.Sat∂ B)
  m = m0

  P₁ : PresentationC (LogOSSignature.Cosp Sig) X SatX
  P₁ = canonicalPresentation SatX

  P₂ : PresentationC (LogOSSignature.∂Cosp Sig)
                    (BulkBoundary.Con_bnd (Kernel.BB K))
                    (BoundaryIO.Sat∂ B)
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
  compile≈interp t pres p φ = Prop.↔-sym (H.translate-unique t pres p φ)
