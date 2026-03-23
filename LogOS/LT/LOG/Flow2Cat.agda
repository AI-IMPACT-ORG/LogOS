{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Flow2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Flow-preserving morphisms as a thin 2-category (design-target spec).
--
-- See spec v5.8 “Normalisation doctrine”, subsection “Morphisms preserving flow”.
-- Implemented as a Σ-decoration (Grothendieck-style; refinement inherited from the base) of a displayed structure over `LOG`.
--
-- Displayed objects: a chosen guarded closure on the boundary of a kernel.
-- Displayed morphisms: Flow-naturality (the single lax coherence inequality).
-- 2-cells: inherited boundary-driven observational refinements (`_⇒∂_`) on the underlying kernel morphisms.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom.Core using (KernelHom)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.HomFlow using (KernelHomFlow; idKernelHomFlow; composeKernelHomFlow)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data FlowTag : Set where
  flowTag : FlowTag

flowTagId : ℕ
flowTagId = 19

FlowDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode}) (lsuc (ℓ ⊔ ℓRel)) (lsuc (ℓ ⊔ ℓRel))
FlowDisplayed {ℓ} {ℓRel} {ℓCode} =
  record
    { Ob = λ K → GuardedClosure (bnd K)
    ; HomD = λ {K} {K'} (h : KernelHom K K') (GC : GuardedClosure (bnd K)) (GC' : GuardedClosure (bnd K'))
      → KernelHomFlow GC GC' h
    ; idD = idKernelHomFlow
    ; compD = composeKernelHomFlow
    }

module Port {ℓ ℓRel ℓCode : Level} =
  Template.SingletonLayer
    flowTagId
    {Tag = FlowTag}
    (FlowDisplayed {ℓ} {ℓRel} {ℓCode})

flowSig
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) flowTagId FlowTag
flowSig {ℓ} {ℓRel} {ℓCode} =
  Port.portSig {ℓ} {ℓRel} {ℓCode}

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)
