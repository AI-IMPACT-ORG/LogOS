{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.RefinementSurface where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (refl⊑)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)

import LogOS.API.Kernel as KernelAPI

K : KernelAPI.Kernel lzero lzero lzero
K = KernelAPI.BoundaryKernel UnitPreorder₀

boundaryIdRefines
  : KernelAPI._⇒∂_
      {K = K}
      {K' = K}
      (KernelAPI.idKernelHom K)
      (KernelAPI.idKernelHom K)
boundaryIdRefines c =
  refl⊑ UnitPreorder₀
    {c = KernelAPI.transportObs (KernelAPI.idKernelHom K) c}

implementationIdRefines
  : KernelAPI.ImplementationView._⇒_
      {K = K}
      {K' = K}
      (KernelAPI.idKernelHom K)
      (KernelAPI.idKernelHom K)
implementationIdRefines γ =
  refl⊑ UnitPreorder₀
    {c = KernelAPI.ImplementationView.obs (KernelAPI.idKernelHom K) γ}
