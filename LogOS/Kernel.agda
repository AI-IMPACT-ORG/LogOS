{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Core as Core hiding (FlowCode)

-- Kernel = shared shape + ungraded guarded closure (G-tier).
--
-- The shared fields are factored out into `KernelShape` to avoid duplication with
-- graded kernels. We then “open” the shape publicly so the projection names stay
-- stable across the codebase.

record Kernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    -- G-tier: guarded closure on boundary constraints (stable truth).
    GTruth : Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (Core.KernelShape.BB shape))

    -- Kernel coherence (laws) for the shared shape + guarded tier.
    laws : Core.KernelLaws shape GTruth

  open Core.KernelLaws laws public

-- Derived code-level Flow (Guard ∘ body)

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) → Kernel.Code K → Kernel.Code K
FlowCode K = Core.FlowCode (Kernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ)
    ≡ Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K)
        (Kernel.Body∂ K (Kernel.decode K γ))
decode-FlowCode {Sig = Sig} {Q = Q} K γ =
  trans (Kernel.guard-decode K (Kernel.Body K γ))
        (cong (Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K))
              (Kernel.body-decode K γ))

-- Optional graded extension (kept under a separate namespace to avoid clashes).
import LogOS.Kernel.Graded as Gradedₜ
module Graded = Gradedₜ
