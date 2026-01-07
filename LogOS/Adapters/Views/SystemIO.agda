{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Views.SystemIO where

-- “One-liner” rebasing of toolchains (SystemIO) along canonical LogOS views.
--
-- This module composes:
-- - canonical satisfaction morphisms induced by views (`Adapters.Views.SatMor`)
-- - the generic pullback construction for proof-carrying tools (`Ports.Semantic.SystemIO`)
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

open import LogOS.Kernel.LogicKernel using (LogicKernel)
open import LogOS.Kernel.LogicKernel.Hom using (LogicKernelHom)
open import LogOS.Kernel.LogicKernel.Reindex using (reindexLogicKernel)

open import LogOS.Adapters.Views.SatMor
  using
    ( satMor-reindexKernel-boundary
    ; satMor-reindexLogicKernel-boundary
    ; satMor-of-KernelHom-boundary
    ; satMor-of-LogicKernelHom-boundary
    ; KernelHomBoundarySat
    ; LogicKernelHomBoundarySat
    )

open import LogOS.Ports.Semantic.InterlinguaCore using (canonicalPresentation)
open import LogOS.Ports.Semantic.SystemIO using (SystemIO; SystemIO↑; rebaseAlongSatMor)

-- Signature reindexing: pull a `SystemIO` over `K` back to the reindexed kernel.

reindexSystemIO-boundary
  : ∀ {ℓName ℓ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → SystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig₂)
      (BulkBoundary.Con_bnd (Kernel.BB K))
      (Kernel.Sat_H_bnd K)
  → SystemIO↑ {ℓForm = ℓ} {ℓLift = ℓ} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig₁)
      (BulkBoundary.Con_bnd (Kernel.BB K))
      (Kernel.Sat_H_bnd (reindexKernel σ K))
reindexSystemIO-boundary σ K sys =
  let
    K₁ = reindexKernel σ K
    m  = satMor-reindexKernel-boundary σ K
    P₁ = canonicalPresentation (Kernel.Sat_H_bnd K₁)
  in
  rebaseAlongSatMor m P₁ sys

reindexSystemIO-logicKernel-boundary
  : ∀ {ℓName ℓ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : LogicKernel Sig₂ Q)
  → SystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig₂)
      (BulkBoundary.Con_bnd (LogicKernel.BB K))
      (LogicKernel.Sat_H_bnd K)
  → SystemIO↑ {ℓForm = ℓ} {ℓLift = ℓ} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig₁)
      (BulkBoundary.Con_bnd (LogicKernel.BB K))
      (LogicKernel.Sat_H_bnd (reindexLogicKernel σ K))
reindexSystemIO-logicKernel-boundary σ K sys =
  let
    K₁ = reindexLogicKernel σ K
    m  = satMor-reindexLogicKernel-boundary σ K
    P₁ = canonicalPresentation (LogicKernel.Sat_H_bnd K₁)
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
  → SystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig)
      (BulkBoundary.Con_bnd (Kernel.BB K₂))
      (Kernel.Sat_H_bnd K₂)
  → SystemIO↑ {ℓForm = ℓ} {ℓLift = ℓ} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig)
      (BulkBoundary.Con_bnd (Kernel.BB K₁))
      (Kernel.Sat_H_bnd K₁)
rebaseAlongKernelHom-boundary {K₁ = K₁} h hs sys =
  let
    m  = satMor-of-KernelHom-boundary h hs
    P₁ = canonicalPresentation (Kernel.Sat_H_bnd K₁)
  in
  rebaseAlongSatMor m P₁ sys

rebaseAlongLogicKernelHom-boundary
  : ∀ {ℓName ℓ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K₁ K₂ : LogicKernel Sig Q}
    (h  : LogicKernelHom K₁ K₂)
    (hs : LogicKernelHomBoundarySat K₁ K₂ h)
  → SystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig)
      (BulkBoundary.Con_bnd (LogicKernel.BB K₂))
      (LogicKernel.Sat_H_bnd K₂)
  → SystemIO↑ {ℓForm = ℓ} {ℓLift = ℓ} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig)
      (BulkBoundary.Con_bnd (LogicKernel.BB K₁))
      (LogicKernel.Sat_H_bnd K₁)
rebaseAlongLogicKernelHom-boundary {K₁ = K₁} h hs sys =
  let
    m  = satMor-of-LogicKernelHom-boundary h hs
    P₁ = canonicalPresentation (LogicKernel.Sat_H_bnd K₁)
  in
  rebaseAlongSatMor m P₁ sys
