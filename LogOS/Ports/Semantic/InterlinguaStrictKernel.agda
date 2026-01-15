{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.InterlinguaStrictKernel where

-- Canonical translation from strict formulas to any boundary port:
-- compile = Interp ∘ TransH, and it is unique up to satisfaction.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con using (BulkBoundary)

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

open import LogOS.Kernel
import LogOS.Kernel.Boundary as KBoundary

import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero
open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC; canonicalPresentation)
import LogOS.Ports.Semantic.Interlingua as Interlingua
open import LogOS.Adapters.Views.SatMor using (satMor-strict-to-boundary)

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm : Level}
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  where

  B : BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  B = KBoundary.boundaryIO K

  module ST = Truth.StrictTruth Sig

  SatS : LogOSSignature.Cosp Sig → Kernel.Fml K → Set ℓ
  SatS = ST.StrictLayer.Sat_S (Kernel.Strict K)

  P₁ : PresentationC (LogOSSignature.Cosp Sig) (Kernel.Fml K) SatS
  P₁ = canonicalPresentation SatS

  P₂ : PresentationC (LogOSSignature.∂Cosp Sig)
                    (BulkBoundary.Con_bnd (Kernel.BB K))
                    (BoundaryIO.Sat∂ B)
  P₂ = Interlingua.toPresentationC B P

  m = satMor-strict-to-boundary K
  module H = Hetero.For m P₁ P₂

  compile : Kernel.Fml K → BoundaryPort.Form P
  compile = H.translate

  compile-preserves-Sat
    : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K)
    → Prop._↔_
        (ST.StrictLayer.Sat_S (Kernel.Strict K) w φ)
        (BoundaryPort.SatF P (LogOSSignature.to∂ Sig w) (compile φ))
  compile-preserves-Sat = H.translate-preserves-Sat

  compile-unique
    : ∀ (t : Kernel.Fml K → BoundaryPort.Form P)
    → H.SemPreserving t
    → H._≈⇒_ t compile
  compile-unique = H.translate-unique

  interp-TransH : Kernel.Fml K → BoundaryPort.Form P
  interp-TransH φ = BoundaryPort.Interp P (Kernel.TransH K φ)

  interp-TransH-preserves-Sat
    : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K)
    → Prop._↔_
        (ST.StrictLayer.Sat_S (Kernel.Strict K) w φ)
        (BoundaryPort.SatF P (LogOSSignature.to∂ Sig w) (interp-TransH φ))
  interp-TransH-preserves-Sat w φ =
    Prop.↔-trans
      (Kernel.coh-LH K w φ)
      (Prop.↔-trans
        (Kernel.sat-coh K w (Kernel.TransH K φ))
        (BoundaryPort.Sat∂≈F P (LogOSSignature.to∂ Sig w) (Kernel.TransH K φ)))

  compile≈interp-TransH
    : H._≈⇒_ compile interp-TransH
  compile≈interp-TransH = H.translate-unique interp-TransH interp-TransH-preserves-Sat

  compile≈interp : H._≈⇒_ compile interp-TransH
  compile≈interp = compile≈interp-TransH
