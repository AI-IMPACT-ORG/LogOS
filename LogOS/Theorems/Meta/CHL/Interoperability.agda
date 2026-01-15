{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Interoperability where

-- Interoperability view: translations between ports are determined by shared
-- boundary semantics, i.e. a CHL-style “meaning-preserving” view at the boundary.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Syntax.Prop as Prop
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Kernel
import LogOS.Kernel.Boundary as KBoundary
import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Ports.Semantic.InterlinguaStrictKernel as StrictKernel
import LogOS.Ports.Semantic.InterlinguaCodeKernel as CodeKernel
import LogOS.Theorems.Meta.Transpiler as Transpilerₜ

open Interop using (PortAdapter)

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm₁ ℓForm₂ : Level}
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  where

  B = KBoundary.boundaryIO K
  module I = Interop.For B P₁ P₂

  open I public using (Adapter≈; canonicalAdapter; adapter-unique)

  -- CHL phrasing: any adapter is meaning-preserving by construction.
  preserves-sat
    : ∀ (A : PortAdapter B P₁ P₂) (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
    → Prop._↔_
        (BoundaryPort.SatF P₁ p φ)
        (BoundaryPort.SatF P₂ p (PortAdapter.map A φ))
  preserves-sat A = PortAdapter.preserves-Sat A

  canonical-preserves-sat
    : ∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
    → Prop._↔_
        (BoundaryPort.SatF P₁ p φ)
        (BoundaryPort.SatF P₂ p (PortAdapter.map canonicalAdapter φ))
  canonical-preserves-sat = preserves-sat canonicalAdapter

module Strict
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm : Level}
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  where
  module SK = StrictKernel.For K P
  open SK public using
    ( compile
    ; compile-preserves-Sat
    ; compile-unique
    ; compile≈interp-TransH
    )

  module Transpiler where
    module T = Transpilerₜ.Hetero SK.m SK.P₁ SK.P₂
    open T public using (Transpiler; transpiler-unique; transpiler-correct)

    compile-transpiler : T.Transpiler
    compile-transpiler =
      T.transpiler-from-translation SK.compile SK.compile-preserves-Sat

module Code
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm : Level}
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  where
  module CK = CodeKernel.For K P
  open CK public using
    ( compile
    ; compile-preserves-Sat
    ; compile-unique
    ; compile≈interp-decode
    )

  module Transpiler where
    module T = Transpilerₜ.Hetero CK.m CK.P₁ CK.P₂
    open T public using (Transpiler; transpiler-unique; transpiler-correct)

    compile-transpiler : T.Transpiler
    compile-transpiler =
      T.transpiler-from-translation CK.compile CK.compile-preserves-Sat
