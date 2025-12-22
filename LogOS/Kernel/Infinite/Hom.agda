{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Infinite.Hom where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Infinite

-- Morphisms between infinite kernels.
--
-- We keep this deliberately minimal and LogOS-native:
-- a morphism is a Kernel homomorphism together with Flow preservation.
-- (Preservation of ωCPO structure is an optional separate upgrade.)

record InfiniteKernelHom {ℓ : Level}
                         {Sig : LogOSSignature ℓ}
                         {Q   : QAdapter ℓ}
                         (IK₁ IK₂ : InfiniteKernel Sig Q)
                         : Set (lsuc (lsuc ℓ)) where
  field
    hom : KernelHom (InfiniteKernel.K IK₁) (InfiniteKernel.K IK₂)
    flow  : KernelHomFlow (InfiniteKernel.K IK₁) (InfiniteKernel.K IK₂) hom
