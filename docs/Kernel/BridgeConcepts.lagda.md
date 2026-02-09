<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Bridge Concepts (Kernel Sidecar)

```agda
{-# OPTIONS --safe #-}
module docs.Kernel.BridgeConcepts where

open import LogOS.Prelude
open import LogOS.API.Bridges

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.UngradedKernel using (UngradedKernel)
open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.FromUngradedKernel using () renaming (asKernel to asKernelUngraded')
open import LogOS.Kernel.FromGradedKernel using () renaming (asKernel to asKernelGraded')

import LogOS.Kernel.Tiers as Tiers
import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub
import LogOS.Computation.ProcessLimit as ProcessLimit
import LogOS.Computation.ProcessLimitSub2Cat as ProcessLimitSub2Cat

private
  asKernelUngraded-exists : _
  asKernelUngraded-exists = asKernelUngraded'

  asKernelGraded-exists : _
  asKernelGraded-exists = asKernelGraded'

  flowSub-wrapper-exists : _
  flowSub-wrapper-exists = FlowSub.With.Hom₁ᶠ

  run∞-exists : _
  run∞-exists = ProcessLimit.For.run∞

  preserves-run∞-exists : _
  preserves-run∞-exists = ProcessLimitSub2Cat.For.preserves-run∞

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where
  module T = Tiers.For K

  decodeView-exists : _
  decodeView-exists = T.decodeView

  satR-bridge-exists : _
  satR-bridge-exists = T.coh-SR
```

This sidecar names the canonical bridge concepts in one place.

Bridge concept (working definition)
-----------------------------------
A bridge is a typed connector that transports structure across layers without
adding axioms. In this repository, bridges are usually one of:

- Representation bridge: map one kernel representation into another (`asKernelUngraded`, `asKernelGraded`).
- Tier bridge: expose S/H/G/R relations as derived views (`Tiers.For`).
- Flow bridge: package a property-preserving 1-cell as a sub-2-category (`FlowSub2Cat.With`).
- Limit bridge: transport `run∞` under continuity-marked lax morphisms (`ProcessLimit.TransportLax.run∞-map≤`).

Why this sidecar exists
-----------------------
The code already had these constructions spread across kernel and computation
modules. This page gives a single canonical vocabulary so docs and APIs can
refer to bridges consistently.
