{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.CanonicalPorts where

-- Canonical port/presentation constructors derived from a kernel.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

open import LogOS.Kernel
import LogOS.Kernel.Boundary as KBoundary

open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC; canonicalPresentation)
import LogOS.Ports.Semantic.Interlingua as Interlingua
import LogOS.Ports.Semantic.InterlinguaStrictKernel as StrictKernel
import LogOS.Ports.Semantic.InterlinguaCodeKernel as CodeKernel

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  B : BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  B = KBoundary.boundaryIO K

  -- Canonical boundary port.
  BoundaryPort∂
    : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
  BoundaryPort∂ = canonicalPort B

  -- Code as a boundary port: decode is the import, encode is the export.
  CodePort
    : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
  CodePort =
    record
      { Sem =
          record
            { Form = Kernel.Code K
            ; SatF = λ p γ → Kernel.Sat_H_bnd K p (Kernel.decode K γ)
            ; Interp = Kernel.encode K
            ; Sat∂≈F = λ p c →
                let
                  eq = Kernel.decode∘encode K c
                in
                Prop.intro
                  (λ sat → subst (λ x → Kernel.Sat_H_bnd K p x) (sym eq) sat)
                  (λ sat → subst (λ x → Kernel.Sat_H_bnd K p x) eq sat)
            }
      ; Import = Kernel.decode K
      ; SatF≈∂ = λ _ _ → Prop.↔-refl
      }

  -- Convenience: translate between kernel code and any other boundary port over
  -- the same canonical boundary satisfaction.

  code→Port
    : ∀ {ℓForm : Level}
      (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
    → Kernel.Code K → BoundaryPort.Form P
  code→Port P = Interlingua.translate B CodePort P

  port→Code
    : ∀ {ℓForm : Level}
      (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
    → BoundaryPort.Form P → Kernel.Code K
  port→Code P = Interlingua.translate B P CodePort

  -- Kernel closure as a ported closure: Box = Extend Flow on the canonical CodePort.

  Flow∂ = Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K)

  Box≡ExtendFlow
    : ∀ (γ : Kernel.Code K)
    → Box K γ ≡ BoundaryPort.Extend CodePort Flow∂ γ
  Box≡ExtendFlow _ = refl

  -- Strict formulas as a canonical presentation (not a boundary port).
  module ST = Truth.StrictTruth Sig

  SatS : LogOSSignature.Cosp Sig → Kernel.Fml K → Set ℓ
  SatS = ST.StrictLayer.Sat_S (Kernel.Strict K)

  StrictPresentation : PresentationC (LogOSSignature.Cosp Sig) (Kernel.Fml K) SatS
  StrictPresentation = canonicalPresentation SatS

  -- Canonical strict compilation into the boundary port.
  module StrictInterlingua where
    module SK = StrictKernel.For K BoundaryPort∂
    open SK public using
      ( compile
      ; compile-preserves-Sat
      ; compile-unique
      ; interp-TransH
      ; compile≈interp-TransH
      )
    compile≈interp = compile≈interp-TransH

  -- Canonical code compilation into the boundary port.
  module CodeInterlingua where
    module CK = CodeKernel.For K BoundaryPort∂
    open CK public using
      ( compile
      ; compile-preserves-Sat
      ; compile-unique
      ; interp-decode
      ; compile≈interp-decode
      )
    compile≈interp = compile≈interp-decode
