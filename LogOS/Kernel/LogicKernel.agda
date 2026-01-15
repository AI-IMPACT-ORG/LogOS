{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel where

-- Generic kernel interface intended for the Curry–Howard–Lambek “single system”
-- view: an S/H/code kernel shape, together with a parameterised guarded (G) tier.
--
-- This module introduces no new axioms: it only repackages existing structures
-- (unguarded and graded) behind a shared interface, enabling uniform 2-categorical
-- refinements and irreversible (preorder-enriched) reasoning.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Core as Core hiding (FlowCode)

-- A minimal, “step-indexed” guarded tier over a boundary constraint poset.
--
-- `Step` is:
-- - `⊤` for ungraded kernels (one global step),
-- - `Scale` for graded kernels (resource-indexed step),
-- but we keep it abstract so we can express both uniformly.
--
-- Only the saturation step `sat` is assumed to form a closure (mono/infl/idemp-lax),
-- matching existing `GuardedClosure` and `GradedClosure` interfaces.

record GTier {ℓ : Level} (Q : QAdapter ℓ) (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    Step : Set ℓ
    step : Step
    sat  : Step

    Flow : Step → Con → Con
    mono : ∀ {g c c'} → _⊑_ c c' → _⊑_ (Flow g c) (Flow g c')

    infl-sat  : ∀ c → _⊑_ c (Flow sat c)
    idemp-sat : ∀ c → _⊑_ (Flow sat (Flow sat c)) (Flow sat c)

    Th*       : Con
    Th*-fixed : (_⊑_ Th* (Flow sat Th*)) × (_⊑_ (Flow sat Th*) Th*)

open GTier public

-- A “logic kernel”: shared S/H/code shape + a parameterised guarded tier,
-- plus the coherence laws relating code-level `Guard` to the guarded step and
-- the distinguished decoded fixed point to `Th*`.

record LogicKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    shapeLaws : Core.KernelShapeLaws shape
  open Core.KernelShapeLaws shapeLaws public

  field
    G : GTier Q (BulkBoundary.bnd (Core.KernelShape.BB shape))

    guard-decode
      : ∀ γ →
        Core.KernelShape.decode shape (Core.KernelShape.Guard shape γ)
          ≡ GTier.Flow G (GTier.step G) (Core.KernelShape.decode shape γ)

    decode-γ*
      : Core.KernelShape.decode shape (Core.KernelShape.γ* shape)
        ≡ GTier.Th* G

-- Derived operational step on code: Guard ∘ Body (same as Kernel.FlowCode).

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → LogicKernel.Code K → LogicKernel.Code K
FlowCode K = Core.FlowCode (LogicKernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → LogicKernel.decode K (FlowCode K γ)
    ≡ GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K))
        (LogicKernel.Body∂ K (LogicKernel.decode K γ))
decode-FlowCode K γ =
  trans (LogicKernel.guard-decode K (LogicKernel.Body K γ))
        (cong (GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K)))
              (LogicKernel.body-decode K γ))
