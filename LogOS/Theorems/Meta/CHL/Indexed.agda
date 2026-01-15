{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Indexed where

-- Indexed view: signature reindexing preserves code and refinement on-the-nose.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel
import LogOS.Kernel.Reindex as Reindex

import LogOS.Theorems.Meta.CHL.Core as Core

module For
  {ℓ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (sigma : SigHom Sig₁ Sig₂)
  (K : Kernel Sig₂ Q)
  where

  Ksigma : Kernel Sig₁ Q
  Ksigma = Reindex.reindexKernel sigma K

  module C = Core.For Ksigma
  open C public

  reindex-code : Kernel.Code Ksigma ≡ Kernel.Code K
  reindex-code = Reindex.reindex-Code sigma K

  reindex-decode : ∀ gamma → Kernel.decode Ksigma gamma ≡ Kernel.decode K gamma
  reindex-decode = Reindex.reindex-decode sigma K

  reindex-box : ∀ gamma → FlowCode Ksigma gamma ≡ FlowCode K gamma
  reindex-box = Reindex.reindex-FlowCode sigma K

module WithFml
  {ℓ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (sigma : SigHom Sig₁ Sig₂)
  (K : Kernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → Kernel.Fml K)
  where

  Ksigma : Kernel Sig₁ Q
  Ksigma = Reindex.reindexKernelWithFml sigma K mapFml

  module C = Core.For Ksigma
  open C public

  reindex-code : Kernel.Code Ksigma ≡ Kernel.Code K
  reindex-code = Reindex.reindexWithFml-Code sigma K mapFml

  reindex-decode : ∀ gamma → Kernel.decode Ksigma gamma ≡ Kernel.decode K gamma
  reindex-decode = Reindex.reindexWithFml-decode sigma K mapFml

  reindex-box : ∀ gamma → FlowCode Ksigma gamma ≡ FlowCode K gamma
  reindex-box = Reindex.reindexWithFml-FlowCode sigma K mapFml
