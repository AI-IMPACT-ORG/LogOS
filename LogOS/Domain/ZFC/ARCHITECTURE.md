<!--
LogOS: an Agda research library for foundational logic system architecture.
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

- Curated pack bundle: `LogOS/Packs/ZFC/All.agda`
- WFGraph pack quartets (Assumptions/Claim/Pack/mkPack): `LogOS/Packs/ZFC/WFGraph.agda`
- WFGraph route (worked semantics pipeline): `LogOS/Domain/ZFC/WFGraph/Surface.agda`
- Proof-theoretic layer (FOL + ZF/ZFC sentences + soundness): `LogOS/ObjectLogic/ZFC/All.agda`
- Publication-facing ledger: `docs/Applications/ZFC.lagda.md`

Layering (ports/adapters)
-------------------------

1. **Kernel (core)**
   - `LogOS/*`
   - Provides the reflective boundary interface, Flow, and the endo/tensor DSL.

2. **Set-theory ports**
   - First-order/coded interface: `LogOS/Domain/ZFC/SetTheory/FormulaPack.agda` (`ZFAxiomsᶠ`, `ZFCAxiomsᶠ`)
   - Definable/coded interface: `LogOS/Domain/ZFC/SetTheory/DefinablePack.agda`
   - Definable → formula-pack bridge: `LogOS/Domain/ZFC/SetTheory/FormulaFromDefinable.agda`
   - Meta-level convenience interface (explicitly stronger): `LogOS/Domain/ZFC/SetTheory/Pack.agda`

3. **Adapters / plumbing**
   - `LogOS/Domain/ZFC/SetTheory/FromZFAxioms.agda` (`ZFAxioms → CumulativeHierarchy`)
   - `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda` (`CumulativeHierarchy → StageToCH`, with optional `StageToCH-fromCH-μFlow` under `OmegaCPO` + `FiniteFirst`)
   - `LogOS/Domain/ZFC/SetTheory/CumulativeSurface.agda` (`StageToCH → ZFDsl`)

4. **One worked model route**
   - `LogOS/Domain/ZFC/WFGraph/*`
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

Supplementary alternate routes live under `LogOS/Domain/ZFC/Supplementary/*` and are not
re-exported from the curated pack surface `LogOS.Packs.ZFC.All`. If you need them
explicitly, import the corresponding `LogOS/Domain/ZFC/*` module directly.
