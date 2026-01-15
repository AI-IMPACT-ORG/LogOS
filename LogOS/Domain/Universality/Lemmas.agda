{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Lemmas where

open import LogOS.Prelude
open import LogOS.Domain.Universality.Core as U
open import LogOS.Domain.Universality.KernelRich
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Initial
open import LogOS.Free.Constraints as FreeC

-- Canonical FreeKernel and fold into the universality kernel
FK : Kernel Sig Q
FK = InitialKernel.FreeK (build Sig Q HWorld)

h : KernelHom FK UKR
h = InitialKernel.foldK (build Sig Q HWorld) UKR

-- Definitional reduction lemmas for mapped codes under the canonical fold
eq-dT : KernelHom.mapCode h FreeC.I∂ ≡ U.CoreT (U.mkT 0 0)
eq-dT = refl

eq-dF : KernelHom.mapCode h (FreeC.bnd FreeC.Ib) ≡ U.CoreC (U.mkC 0)
eq-dF = refl
