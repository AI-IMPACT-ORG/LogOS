<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

ZF/ZFC Interpretation Architecture
=================================

This note describes the production layout of the LogOS ZF/ZFC development:
stable entrypoints, the core layering, and which pieces are explicitly
experimental.

Stable entrypoints
------------------

- Stable lock surface: `LogOS/Packs/ZFC/Surface.agda` (umbrella: `LogOS/Packs/ZFC/All.agda`)
- WFGraph pack quartets (Assumptions/Claim/Pack/mkPack): `LogOS/Packs/ZFC/WFGraph.agda`
- WFGraph route (worked semantics pipeline): `LogOS/ZFC/WFGraph/Surface.agda`
- Proof-theoretic layer (FOL + ZF/ZFC sentences + soundness): `LogOS/ObjectLogic/ZFC/All.agda`
- Publication-facing ledger: `docs/Applications/ZFC.lagda.md`

Layering (ports/adapters)
-------------------------

1. **Kernel (core)**
   - `LogOS/*`
   - Provides the reflective boundary interface, Flow, and the endo/tensor DSL.

2. **Set-theory ports**
   - First-order/coded interface: `LogOS/ZFC/SetTheory/FormulaPack.agda` (`ZFAxiomsᶠ`, `ZFCAxiomsᶠ`)
   - Definable/coded interface: `LogOS/ZFC/SetTheory/DefinablePack.agda`
   - Definable → formula-pack bridge: `LogOS/ZFC/SetTheory/FormulaFromDefinable.agda`
   - Meta-level convenience interface (explicitly stronger): `LogOS/ZFC/SetTheory/Pack.agda`

3. **Adapters / plumbing**
   - `LogOS/ZFC/SetTheory/FromZFAxioms.agda` (`ZFAxioms → CumulativeHierarchy`)
   - `LogOS/ZFC/SetTheory/StageToCHFromHierarchy.agda` (`CumulativeHierarchy → StageToCH`, with optional `StageToCH-fromCH-μFlow` under `OmegaCPO` + `FiniteFirst`)
   - `LogOS/ZFC/SetTheory/CumulativeSurface.agda` (`StageToCH → ZFDsl`)

4. **One worked model route**
   - `LogOS/ZFC/WFGraph/*`
   - Interprets sets as nodes in a well-founded membership graph with `sup`
     constructors, then exposes both the definable/formula-pack view and the
     optional meta-level view (under explicit representability assumptions).

5. **Proof-theoretic packaging**
   - `LogOS/ObjectLogic/FOL/*` gives syntax + ND + soundness.
     The ND calculus is intuitionistic; classical reasoning is an explicit extra
     assumption on top.
   - `LogOS/ObjectLogic/ZFC/Axioms.agda` states ZF axioms as FOL sentences; and, given a
     `ZFCAxiomsᶠ` witness, internalises Choice as a sentence `Choiceᶠ` and proves it
     valid.

Experimental / non-core modules
-------------------------------

Supplementary alternate routes live under `LogOS/ZFC/Supplementary/*` and are not
re-exported from the stable lock surface `LogOS.Packs.ZFC.Surface`. If you need them
explicitly, import the corresponding `LogOS/ZFC/*` module directly.
