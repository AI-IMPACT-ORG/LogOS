{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
open import LogOS.Minimal.Con using (ConPreorder; MonoOn; BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

open import LogOS.Kernel
import LogOS.Boundary.FromKernel as KBoundary
import LogOS.Kernel.Shape as KCore

import LogOS.Ports.Semantic.InterlinguaKernelLayer as KernelLayer
import LogOS.Ports.Semantic.Interoperability as Interop
open import LogOS.Adapters.Views.SatMor using (satMor-code-to-boundary)
import LogOS.Minimal.MuFusion as MuFusion

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

  module KL = KernelLayer.For K P (Kernel.Code K) SatR (satMor-code-to-boundary K)
  open KL public using
    ( P₁
    ; P₂
    ; m
    ; compile
    ; compile-preserves-Sat
    ; compile-unique
    ; SemPreserving
    ; _≈⇒_
    ; SatF₂↑
    )

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
    : _≈⇒_ compile interp-decode
  compile≈interp-decode = KL.compile≈interp interp-decode interp-decode-preserves-Sat

  compile≈interp : _≈⇒_ compile interp-decode
  compile≈interp = compile≈interp-decode

  -- -------------------------------------------------------------------------
  -- Limit/stabilisation transport (μ-level) for kernel code compilation.
  --
  -- Under an explicit ωCPO structure on the boundary preorder, we can lift that
  -- ωCPO structure to the code preorder (via `encode`/`decode`) and then apply
  -- μ-fusion through the canonical SatMor (`decode`) to transport exported Kleene μ
  -- fixed points from code to boundary.
  -- -------------------------------------------------------------------------

  module Limit
    (ωBnd : Truth.GuardedCore.OmegaCPO (BulkBoundary.bnd (Kernel.BB K)))
    where
    private
      CPBnd : ConPreorder ℓ
      CPBnd = BulkBoundary.bnd (Kernel.BB K)

      CPCode : ConPreorder ℓ
      CPCode = KCore.CodePreorder (Kernel.shape K)

      module CPB = ConPreorder CPBnd renaming (_⊑_ to _⊑b_)
      module CPC = ConPreorder CPCode renaming (_⊑_ to _⊑c_)

      module GT = Truth.GuardedCore {ℓ = ℓ}
      module MF = MuFusion.For CPCode CPBnd
      module L  = Interop.Limit CPCode CPBnd m P₁ P₂

    -- ωCPO structure on code, induced by the boundary ωCPO via `encode`/`decode`.
    ωCode : GT.OmegaCPO CPCode
    ωCode =
      record
        { ⊥ =
            Kernel.encode K (GT.OmegaCPO.⊥ ωBnd)
        ; isBot = λ γ →
            subst
              (λ x → CPB._⊑b_ x (Kernel.decode K γ))
              (sym (Kernel.decode∘encode K (GT.OmegaCPO.⊥ ωBnd)))
              (GT.OmegaCPO.isBot ωBnd (Kernel.decode K γ))
        ; supω = λ f →
            Kernel.encode K
              (GT.OmegaCPO.supω ωBnd (λ n → Kernel.decode K (f n)))
        ; ub = λ f n →
            subst
              (λ x → CPB._⊑b_ (Kernel.decode K (f n)) x)
              (sym
                (Kernel.decode∘encode K
                  (GT.OmegaCPO.supω ωBnd (λ k → Kernel.decode K (f k)))))
              (GT.OmegaCPO.ub ωBnd (λ k → Kernel.decode K (f k)) n)
        ; least = λ f γ ubF →
            subst
              (λ x → CPB._⊑b_ x (Kernel.decode K γ))
              (sym
                (Kernel.decode∘encode K
                  (GT.OmegaCPO.supω ωBnd (λ n → Kernel.decode K (f n)))))
              (GT.OmegaCPO.least ωBnd
                (λ n → Kernel.decode K (f n))
                (Kernel.decode K γ)
                ubF)
        }

    -- Decode is an ωCPO-map from code (with the induced ωCPO) to the boundary ωCPO.
    decodeOmegaCPOMap : MF.OmegaCPOMap ωCode ωBnd (Kernel.decode K)
    decodeOmegaCPOMap =
      record
        { mono-map = λ le → le
        ; strict⊥  =
            subst
              (λ x → CPB._⊑b_ x (GT.OmegaCPO.⊥ ωBnd))
              (sym (Kernel.decode∘encode K (GT.OmegaCPO.⊥ ωBnd)))
              (CPB.refl {c = GT.OmegaCPO.⊥ ωBnd})
        ; cont-ω   = λ f _ →
            subst
              (λ x →
                CPB._⊑b_ x
                  (GT.OmegaCPO.supω ωBnd (λ n → Kernel.decode K (f n))))
              (sym
                (Kernel.decode∘encode K
                  (GT.OmegaCPO.supω ωBnd (λ n → Kernel.decode K (f n)))))
              (CPB.refl {c = GT.OmegaCPO.supω ωBnd (λ n → Kernel.decode K (f n))})
        }

    MuTransportData
      : (FCode : Kernel.Code K → Kernel.Code K)
      → (FBnd  : BulkBoundary.Con_bnd (Kernel.BB K) → BulkBoundary.Con_bnd (Kernel.BB K))
      → Set (lsuc ℓ)
    MuTransportData = L.MuTransportData↑ ωCode ωBnd

    -- Stronger variant (monotonicity on all target contexts).
    MuTransportDataAllCtx
      : (FCode : Kernel.Code K → Kernel.Code K)
      → (FBnd  : BulkBoundary.Con_bnd (Kernel.BB K) → BulkBoundary.Con_bnd (Kernel.BB K))
      → Set (lsuc ℓ)
    MuTransportDataAllCtx = L.MuTransportData ωCode ωBnd

    -- Derived satisfaction monotonicity for the boundary IO context fragment
    -- actually used by compilation (`mapCtx w = to∂ w`).
    monoSatBnd-to∂
      : ∀ {w : LogOSSignature.Cosp Sig}
          {c d : BulkBoundary.Con_bnd (Kernel.BB K)}
      → CPB._⊑b_ c d
      → BoundaryIO.Sat∂ B (LogOSSignature.to∂ Sig w) c
      → BoundaryIO.Sat∂ B (LogOSSignature.to∂ Sig w) d
    monoSatBnd-to∂ {w = w} le sat =
      KCore.Sat_H_bnd-mono (Kernel.shape K) {w = w} le sat

    mkMuTransportData
      : ∀ {FCode FBnd}
      → MonoOn CPBnd FBnd
      → (∀ γ → CPC._⊑c_ γ (FCode γ))
      → (∀ γ → CPB._⊑b_ (Kernel.decode K (FCode γ)) (FBnd (Kernel.decode K γ)))
      → MuTransportData FCode FBnd
    mkMuTransportData {FCode = FCode} {FBnd = FBnd} monoFBnd inflFCode comm =
      record
        { Mω = decodeOmegaCPOMap
        ; monoF₂ = monoFBnd
        ; inflF₁ = inflFCode
        ; comm = comm
        ; monoSat₂↑ = λ {w} → monoSatBnd-to∂ {w = w}
        }

    compile-μ≤
      : ∀ {FCode FBnd}
      → MuTransportData FCode FBnd
      → ∀ w
      → SatF₂↑ w (compile (Truth.GuardedCore.Kleene.μ ωCode FCode))
      → SatF₂↑ w (BoundaryPort.Interp P (Truth.GuardedCore.Kleene.μ ωBnd FBnd))
    compile-μ≤ = L.translate-μ≤↑

    compile-preserves-stabilisation≤ = compile-μ≤
