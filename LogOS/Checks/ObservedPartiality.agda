{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ObservedPartiality where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; MonoMap)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; BoundaryKernel; bnd)
open import LogOS.LT.Hom using (KernelHom; idKernelHom)
import LogOS.LT.Theorems.Centering as Centering
open import LogOS.Apps.TuringCategory.Lift using (LiftCP; some)
import LogOS.Apps.TuringCategory.Bridge.KernelToPar as K2Par
import LogOS.Ports.Opacity.Port as Opacity

K : Kernel lzero lzero lzero
K = BoundaryKernel UnitPreorder₀

V : View (Con (bnd K)) (LiftCP (bnd K))
V = record { μ = λ γ → some {CP = bnd K} γ }

Pₒ : K2Par.BoundaryObservationPort K (bnd K)
Pₒ =
  K2Par.mkBoundaryObservationPortFromPort
    {K = K}
    {O = bnd K}
    (Opacity.fromView {X = Con (bnd K)} {O = LiftCP (bnd K)} V)
    (λ {γ} {δ} γ⊑δ → tt)

h : KernelHom K K
h = idKernelHom K

canonicalPackage : K2Par.CompleteObservedPresentationPackage Pₒ h
canonicalPackage =
  K2Par.canonicalCompleteObservedPresentationPackage Pₒ h

manualPackage : K2Par.CompleteObservedPresentationPackage Pₒ h
manualPackage = canonicalPackage

fiber
  : Centering.ContractibleFiber
      (K2Par.CompleteObservedPresentationPackage Pₒ h)
      K2Par.CompleteObservedPresentationPackage≈
fiber = K2Par.completeObservedPresentationFiber Pₒ h

packageContractsToCenter
  : K2Par.CompleteObservedPresentationPackage≈
      manualPackage
      canonicalPackage
packageContractsToCenter =
  Centering.contract fiber manualPackage

packageNoFork
  : K2Par.CompleteObservedPresentationPackage≈
      manualPackage
      canonicalPackage
packageNoFork =
  K2Par.completeObservedPresentationNoFork Pₒ h
    {x = manualPackage}
    {y = canonicalPackage}
