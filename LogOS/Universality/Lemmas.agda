{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Universality.Lemmas where

open import LogOS.Prelude
open import LogOS.Universality.Core as U
open import LogOS.Universality.KernelRich
open import LogOS.API.Kernel
open import LogOS.API.Kernel.UngradedKernel.Initial
open import LogOS.Minimal.Constraints as FreeC
open import LogOS.Minimal.ConAlg using (ConAlgHom≡)

-- Canonical FreeKernel and fold into the universality kernel
FK : Kernel Sig Q
FK = asKernelUngraded (InitialKernel.FreeK (build Sig Q HWorld))

h : KernelHom FK UKR
h =
  record
    { con-hom    = FreeC.fold≡ (conAlgOf UKR)
    ; mapCode    = λ γ →
        Kernel.encode UKR
          (ConAlgHom≡.map∂ (FreeC.fold≡ (conAlgOf UKR)) (Kernel.decode FK γ))
    ; map-encode =
        λ c →
          cong
            (λ x →
              Kernel.encode UKR
                (ConAlgHom≡.map∂ (FreeC.fold≡ (conAlgOf UKR)) x))
            (Kernel.decode∘encode FK c)
    ; map-decode =
        λ γ → Kernel.decode∘encode UKR
                (ConAlgHom≡.map∂ (FreeC.fold≡ (conAlgOf UKR)) (Kernel.decode FK γ))
    }

-- Definitional reduction lemmas for mapped codes under the canonical fold
eq-dT : KernelHom.mapCode h FreeC.I∂ ≡ U.CoreT (U.mkT 0 0)
eq-dT = refl

eq-dF : KernelHom.mapCode h (FreeC.bnd FreeC.Ib) ≡ U.CoreC (U.mkC 0)
eq-dF = refl
