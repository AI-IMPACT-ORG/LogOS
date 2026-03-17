<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Clarification: “directed type theory” in LogOS (v1.1)

This note clarifies a phrase that is prone to over-reading.

LogOS does **not** (yet) implement a standalone “directed type theory” as a new primitive calculus.
Instead, it enforces a **directed/refinement discipline** across the existing Agda development:

- semantic comparison is by a preorder `⊑` on observable constraints,
- equality `≡` is reserved for strict coherence/bookkeeping,
- any upgrade from mutual refinement `≈` to equality is always an explicit *assumption* (never ambient).
- on public-facing explanatory surfaces, the same refinement relation may be written `≼` when the polarity is easier to read that way.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Clarifications.Directed_Type_Theory where

import LogOS.API.LT
```

What “directed” means here
--------------------------

1. **A boundary is a preorder of constraints.**  
   The primary judgement is refinement/entailment `c ⊑ d` (“`d` is stronger / more informative than `c`”).
   On reader-facing surfaces, the same judgement may be written `c ≼ d`.

2. **Program meaning is directed.**  
   A kernel’s meaning is a map `decode : Code → Con bnd`. The induced comparison on code is the pullback of `⊑`
   along `decode` (so “directed equality” is *by observation*, not by representation).

3. **Coherence is strict only when forced.**  
   Adapters (`KernelHom`) commute with observation by mutual refinement (`≈`) (`decode-mapCode`).
   Upgrading this to strict equality is an explicit, opt-in antisymmetry-based strictification step
   (the repository also uses “classical limit” as an internal label):
   - kernel-level: `Ports.ClassicalLimit` strictifies the refinement-first kernel morphism surface into the explicit `LogOS.API.Strictification.Kernel` lane,
  - stack-level: `LogOS/LT/Ports/PortStack/ClassicalLimit.agda` strictifies an arbitrary `LOG` port stack
    (deriving strict decode law via `LT/LOG/ClassicalLimit2Cat.strictifyDisplayed`; guardrail: `LogOS/Checks/PortStackStrictify.agda`).
   Additional doctrines (Flow, contracts, encode, budgets, …) are expressed as extra *lax* obligations or displayed
   structure.

4. **Global axioms are never smuggled.**  
   If you need extensionality, function extensionality, antisymmetry, classical choice, etc., it must appear as an
   explicit field/parameter in a port/ledger for the relevant pack.

Consequences (reader checklist)
-------------------------------

- If you see `≡`, ask: “is this only coherence/bookkeeping, or is it an equality-strengthening assumption?”
- If a construction claims “equivalence”, check whether it is `≈` (mutual refinement) or `≡` (propositional equality).
- If a proof needs “global coherence”, treat it as an explicit late-stage strictification principle, not as
  kernel-level structure.
- If a theorem uses `KernelHom`, read it as the weak surface first; use
  `docs/Patterns/Clarifications/Weak_vs_Strict_KernelHom.lagda.md` for the explicit upgrade path.

Interpretation note (scope discipline)
-------------------------------------

If you want to read the LT spine as a directed type theory / HoTT / institution / CHL story, treat that as a **view**:
opt-in modules under `LogOS.API.Views` (not part of the default curated kernel surface).
