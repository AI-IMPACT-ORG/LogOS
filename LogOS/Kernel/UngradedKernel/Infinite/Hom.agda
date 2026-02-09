{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Infinite.Hom where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.UngradedKernel.Hom
open import LogOS.Kernel.UngradedKernel.Infinite

-- Morphisms between infinite kernels.
--
-- We keep this deliberately minimal and LogOS-native:
-- a morphism is a UngradedKernel homomorphism together with Flow preservation.
-- (Preservation of ωCPO structure is an optional separate upgrade.)

record InfiniteKernelHom {ℓ : Level}
                         {Sig : LogOSSignature ℓ}
                         {Q   : QAdapter ℓ}
                         (IK₁ IK₂ : InfiniteKernel Sig Q)
                         : Set (lsuc (lsuc ℓ)) where
  field
    hom : UngradedKernelHom (InfiniteKernel.K IK₁) (InfiniteKernel.K IK₂)
    flow  : UngradedKernelHomFlow (InfiniteKernel.K IK₁) (InfiniteKernel.K IK₂) hom
