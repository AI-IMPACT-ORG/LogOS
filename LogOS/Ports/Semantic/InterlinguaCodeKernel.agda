{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.InterlinguaCodeKernel where

-- Canonical translation from kernel code into any boundary port:
-- compile = Interp ∘ decode, unique up to satisfaction.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

open import LogOS.Kernel
import LogOS.Kernel.Boundary as KBoundary

import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero
open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC; canonicalPresentation)
import LogOS.Ports.Semantic.Interlingua as Interlingua
open import LogOS.Adapters.Views.SatMor using (satMor-code-to-boundary)

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm : Level}
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  where

  B : BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  B = KBoundary.boundaryIO K

  SatR : LogOSSignature.Cosp Sig → Kernel.Code K → Set ℓ
  SatR w γ = Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K γ)

  P₁ : PresentationC (LogOSSignature.Cosp Sig) (Kernel.Code K) SatR
  P₁ = canonicalPresentation SatR

  P₂ : PresentationC (LogOSSignature.∂Cosp Sig)
                    (BulkBoundary.Con_bnd (Kernel.BB K))
                    (BoundaryIO.Sat∂ B)
  P₂ = Interlingua.toPresentationC B P

  m = satMor-code-to-boundary K
  module H = Hetero.For m P₁ P₂

  compile : Kernel.Code K → BoundaryPort.Form P
  compile = H.translate

  compile-preserves-Sat
    : ∀ (w : LogOSSignature.Cosp Sig) (γ : Kernel.Code K)
    → Prop._↔_
        (SatR w γ)
        (BoundaryPort.SatF P (LogOSSignature.to∂ Sig w) (compile γ))
  compile-preserves-Sat = H.translate-preserves-Sat

  compile-unique
    : ∀ (t : Kernel.Code K → BoundaryPort.Form P)
    → H.SemPreserving t
    → H._≈⇒_ t compile
  compile-unique = H.translate-unique

  interp-decode : Kernel.Code K → BoundaryPort.Form P
  interp-decode γ = BoundaryPort.Interp P (Kernel.decode K γ)

  interp-decode-preserves-Sat
    : ∀ (w : LogOSSignature.Cosp Sig) (γ : Kernel.Code K)
    → Prop._↔_
        (SatR w γ)
        (BoundaryPort.SatF P (LogOSSignature.to∂ Sig w) (interp-decode γ))
  interp-decode-preserves-Sat w γ =
    BoundaryPort.Sat∂≈F P (LogOSSignature.to∂ Sig w) (Kernel.decode K γ)

  compile≈interp-decode
    : H._≈⇒_ compile interp-decode
  compile≈interp-decode = H.translate-unique interp-decode interp-decode-preserves-Sat

  compile≈interp : H._≈⇒_ compile interp-decode
  compile≈interp = compile≈interp-decode
