{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Views.SatSystemIO where

-- “One-liner” rebasing of toolchains (`SatSystemIO`) along canonical LogOS views.
--
-- This module composes:
-- - canonical satisfaction morphisms induced by views (`Adapters.Views.SatMor`)
-- - the generic pullback construction for proof-carrying tools (`Ports.Semantic.SatSystemIO`)
--
-- The result is intentionally conservative:
-- - across changing signatures/kernels, the rebased system uses the *canonical*
--   presentation (`Form = Con`) for the source satisfaction relation.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)

open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Hom using (KernelHom)
open import LogOS.Kernel.Reindex using (reindexKernel)

open import LogOS.Adapters.Views.SatMor
  using
    ( satMor-reindexKernel-boundary
    ; satMor-of-KernelHom-boundary
    ; KernelHomBoundarySat
    )

open import LogOS.Ports.Semantic.HeteroInterlinguaCore using (canonicalPresentation)
open import LogOS.Ports.Semantic.Core using (boundarySatSystem)
open import LogOS.Ports.Semantic.SatSystemIO using (SatSystemIO; SatSystemIO↑; rebaseAlongSatMor)

-- Signature reindexing: pull a `SatSystemIO` over `K` back to the reindexed kernel.

reindexSatSystemIO-boundary
  : ∀ {ℓName ℓ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → SatSystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (boundarySatSystem {Sig = Sig₂} {BB = Kernel.BB K} (Kernel.Sat_H_bnd K))
  → SatSystemIO↑ {ℓForm = ℓ} {ℓLift = ℓ} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (boundarySatSystem {Sig = Sig₁} {BB = Kernel.BB K} (Kernel.Sat_H_bnd (reindexKernel σ K)))
reindexSatSystemIO-boundary {Sig₁ = Sig₁} σ K sys =
  let
    K₁ = reindexKernel σ K
    m  = satMor-reindexKernel-boundary σ K
    BB = Kernel.BB K
    P₁ = canonicalPresentation (boundarySatSystem {Sig = Sig₁} {BB = BB} (Kernel.Sat_H_bnd K₁))
  in
  rebaseAlongSatMor m P₁ sys

-- Kernel-hom rebasing (requires an explicit satisfaction equivalence witness).


rebaseAlongKernelHom-boundary
  : ∀ {ℓName ℓ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h  : KernelHom K₁ K₂)
    (hs : KernelHomBoundarySat K₁ K₂ h)
  → SatSystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (boundarySatSystem {Sig = Sig} {BB = Kernel.BB K₂} (Kernel.Sat_H_bnd K₂))
  → SatSystemIO↑ {ℓForm = ℓ} {ℓLift = ℓ} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (boundarySatSystem {Sig = Sig} {BB = Kernel.BB K₁} (Kernel.Sat_H_bnd K₁))
rebaseAlongKernelHom-boundary {Sig = Sig} {K₁ = K₁} h hs sys =
  let
    m  = satMor-of-KernelHom-boundary h hs
    BB = Kernel.BB K₁
    P₁ = canonicalPresentation (boundarySatSystem {Sig = Sig} {BB = BB} (Kernel.Sat_H_bnd K₁))
  in
  rebaseAlongSatMor m P₁ sys
