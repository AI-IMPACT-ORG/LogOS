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
import LogOS.API.Bridges as Bridges

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)

private
  asKernelUngraded-exists : _
  asKernelUngraded-exists = Bridges.Repr.asKernelUngraded

  asKernelGraded-exists : _
  asKernelGraded-exists = Bridges.Repr.asKernelGraded

  flowSub-wrapper-exists : _
  flowSub-wrapper-exists = Bridges.Flow.FlowSub2Cat.With.Hom₁ᶠ

  run∞-exists : _
  run∞-exists = Bridges.Limit.Process.For.run∞

  preserves-run∞-exists : _
  preserves-run∞-exists = Bridges.Limit.Sub2Cat.For.preserves-run∞

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where
  module T = Bridges.Tier.Tiers.For K

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

- Representation bridge: map one kernel representation into another (`Bridges.Repr.asKernelUngraded`, `Bridges.Repr.asKernelGraded`).
- Tier bridge: expose S/H/G/R relations as derived views (`Bridges.Tier.Tiers.For`).
- Flow bridge: package a property-preserving 1-cell as a sub-2-category (`Bridges.Flow.FlowSub2Cat.With`).
- Limit bridge: transport `run∞` under continuity-marked lax morphisms (`Bridges.Limit.Process.TransportLax.run∞-map≤`).

Why this sidecar exists
-----------------------
The code already had these constructions spread across kernel and computation
modules. This page gives a single canonical vocabulary so docs and APIs can
refer to bridges consistently.
