<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

WFGraph ZF/ZFC Mechanisation (LogOS.Domain.ZFC)
========================================

This directory contains the LogOS-native mechanisation of (at least) ZF, built
around the idea that *sets are presentations* and semantics lives in the
kernel/boundary interface.

The current “core” path is **WF-graphs + `sup` formation**:

- sets are nodes in a well-founded membership graph (`WFGraph`);
- membership is the edge relation;
- constructors (empty/pairing/union/succ/…​) are realised by a `SupStructure`
  and proven against the graph laws;
- Infinity is obtained naturally by interpreting the iterative-set tree ω (`sup Nat kids`);
- full Separation/Replacement can be obtained by upgrading from *definable*
  schemata under explicit representability assumptions.

Core entrypoints
----------------

- `LogOS/Domain/ZFC/WFGraph/Model.agda` — builds a definable-ZF base pack over a WF-graph carrier
  (membership graph + `sup`), with explicit Extensionality/Powerset/Foundation structures.
- `LogOS/Domain/ZFC/WFGraph/ZFC.agda` — adds ω and produces definable-ZF+Infinity; optionally upgrades
  to full `LogOS.Domain.SetTheory.Pack.ZFAxioms` given explicit representability assumptions.
- `LogOS/Domain/ZFC/WFGraph/Structure.agda` — bundle the WF-graph carrier assumptions into one record
  (`WFGraphStructure`) so the core development has explicit, minimal dependencies.
- `LogOS/Domain/ZFC/WFGraph/Surface.agda` — one-stop façade with two layers:
  - `Definable W` exposes the core definable-ZF(+Infinity) pack (`zfᵈ-Core`),
    plus the formula-pack view (`zfᶠ : ZFAxiomsᶠ K`) where predicates/relations are
    interpreted by membership/graphs.
  - `Full W PR FR` additionally exports `zf : ZFAxioms K`, `CH : CumulativeHierarchy K`,
    `stageToCH : StageToCH K`, and `surface : ZFDsl K`; plus `zfc : ZFCAxioms K` if you
    supply an explicit Choice witness.

Staging / DSL plumbing
----------------------

- Stage packs and `StageToCH`: `LogOS/Domain/SetTheory/Cumulative.agda`
- `LogOS/Domain/SetTheory/StageToCHFromHierarchy.agda` — generic adapter: any `CumulativeHierarchy K`
  can be wrapped as a `StageToCH K` using constant stages and the kernel’s canonical `Th⋆`.
- `LogOS/Domain/SetTheory/CumulativeSurface.agda` — `stageToSurface` promotes `StageToCH` to `ZFDsl`.
- `LogOS/Domain/SetTheory/FromZFAxioms.agda` — converts `ZFAxioms K` to `CumulativeHierarchy K`.
- `LogOS/Domain/SetTheory/Derived.agda` — small derived set constructors/lemmas over `ZFAxioms`
  (e.g. `singleton`, `union₂`).
- `LogOS/Domain/SetTheory/FormulaDerived.agda` — the same style of small derived constructors/lemmas,
  but for the coded/first-order interface `ZFAxiomsᶠ`.

What is (and is not) “ZFC” here?
--------------------------------

- ZF + Infinity is mechanised constructively in the WF-graph route.
- Full ZF Separation/Replacement is available *conditionally* via the explicit
  representability assumptions in `LogOS/Domain/SetTheory/FullUpgradeFromDefinable.agda`.
- Choice (AC) is **not derived**; `ZFCAxioms` is exposed as `ZF + AC` where `AC` is a
  separate, explicit witness (`LogOS/Domain/SetTheory/ChoiceAxiom.agda`).
- The proof-theoretic layer also internalises Choice as a single FOL sentence
  (`LogOS.Logic.ZFC.Axioms.FromZFCAxiomsᶠ.Choiceᶠ`) and proves it valid in any
  `ZFCAxiomsᶠ` model carrying that witness.
- The proof calculus used in `LogOS/Logic/FOL/ND.agda` is **intuitionistic**.
  Classical ZFC can be studied by adding a classical principle explicitly as an
  extra axiom/rule; it is intentionally not assumed by default.

Supplementary / experimental (explicitly non-core)
--------------------------------------------------

The core production route is WFGraph; the following modules are kept for
research/future work and are intentionally not part of the curated surface:

- `LogOS/Domain/ZFC/ClosureEndo.agda` and `LogOS/Domain/ZFC/ClosureModel.agda` (closure/least-fixed-point route scaffold)
- `LogOS/Domain/ZFC/OrdinalScaffold.agda` (ordinal-indexed stage scaffold)
- `LogOS/Domain/ZFC/Supplementary/` (alternate routes, e.g. hereditarily-finite developments)
