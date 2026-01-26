<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
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
- full Separation/Replacement can be obtained in two ways:
  - **directly** from WFGraph `sup` formation (textbook route, see `LogOS/Domain/ZFC/WFGraph/Textbook.agda`);
  - **indirectly** from *definable* schemata under explicit representability assumptions
    (see `LogOS/Domain/ZFC/SetTheory/FullUpgradeFromDefinable.agda`).

Core entrypoints
----------------

- `LogOS/Domain/ZFC/WFGraph/Model.agda` — builds a definable-ZF base pack over a WF-graph carrier
  (membership graph + `sup`), with explicit Extensionality/Powerset/Foundation structures.
- `LogOS/Domain/ZFC/WFGraph/ZFC.agda` — adds ω and produces definable-ZF+Infinity; optionally upgrades
  to full `LogOS.Domain.ZFC.SetTheory.Pack.ZFAxioms` given explicit representability assumptions.
- `LogOS/Domain/ZFC/WFGraph/Structure.agda` — bundle the WF-graph carrier assumptions into one record
  (`WFGraphStructure`) so the core development has explicit, minimal dependencies.
- `LogOS/Domain/ZFC/WFGraph/Surface.agda` — one-stop façade with several layers:
  - `Definable W` exposes the core definable-ZF(+Infinity) pack (`zfᵈ-Core`),
    plus the formula-pack view (`zfᶠ : ZFAxiomsᶠ K`) where predicates/relations are
    interpreted by membership/graphs.
  - `FormulaCoded W` exposes a formula-coded ZF(+Infinity) pack (`zfᶠ : ZFAxiomsᶠ K`)
    where kernel codes are genuine first-order formulas (with explicit parameters),
    and `decode` maps formulas to their extensions in the WFGraph universe.
  - `Full W PR FR` additionally exports `zf : ZFAxioms K`, `CH : CumulativeHierarchy K`,
    `stageToCH : StageToCH K`, and `surface : ZFDsl K`; plus `zfc : ZFCAxioms K` if you
    supply an explicit Choice witness.
  - `Textbook W` exports `zf : ZFAxioms K`, `CH : CumulativeHierarchy K`, `stageToCH : StageToCH K`,
    and `surface : ZFDsl K` **without** PR/FR; plus `zfc : ZFCAxioms K` via `WithChoice`.

Staging / DSL plumbing
----------------------

- Stage packs and `StageToCH`: `LogOS/Domain/ZFC/SetTheory/Cumulative.agda`
- `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda` — generic adapter: any `CumulativeHierarchy K`
  can be wrapped as a `StageToCH K` using constant stages and the kernel’s canonical fixed-point witness `Th⋆`.
  If a model additionally provides a boundary `OmegaCPO` + `FiniteFirst` witness for Flow, `StageToCH-fromCH-μFlow`
  realises the infinity stage by the Kleene μ of Flow (supporting “least fixed point” style claims under explicit assumptions).
- `LogOS/Domain/ZFC/SetTheory/CumulativeSurface.agda` — `stageToSurface` promotes `StageToCH` to `ZFDsl`.
- `LogOS/Domain/ZFC/SetTheory/FromZFAxioms.agda` — converts `ZFAxioms K` to `CumulativeHierarchy K`.
- `LogOS/Domain/ZFC/SetTheory/Derived.agda` — small derived set constructors/lemmas over `ZFAxioms`
  (e.g. `singleton`, `union₂`).
- `LogOS/Domain/ZFC/SetTheory/FormulaDerived.agda` — the same style of small derived constructors/lemmas,
  but for the coded/first-order interface `ZFAxiomsᶠ`.

What is (and is not) “ZFC” here?
--------------------------------

- ZF + Infinity is mechanised constructively in the WF-graph route.
- Full ZF Separation/Replacement is available *conditionally* via the explicit
  representability assumptions in `LogOS/Domain/ZFC/SetTheory/FullUpgradeFromDefinable.agda`.
- Full ZF Separation/Replacement is also available *constructively* in the WFGraph route
  when `supN` formation is available (see `LogOS/Domain/ZFC/WFGraph/Textbook.agda`).
- Choice (AC) is **not derived**; `ZFCAxioms` is exposed as `ZF + AC` where `AC` is a
  separate, explicit witness (`LogOS/Domain/ZFC/SetTheory/ChoiceAxiom.agda`).
- The proof-theoretic layer also internalises Choice as a single FOL sentence
  (`LogOS.ObjectLogic.ZFC.Axioms.FromZFCAxiomsᶠ.Choiceᶠ`) and proves it valid in any
  `ZFCAxiomsᶠ` model carrying that witness.
- The proof calculus used in `LogOS/ObjectLogic/FOL/ND.agda` is **intuitionistic**.
  Classical ZFC can be studied by adding a classical principle explicitly as an
  extra axiom/rule; it is intentionally not assumed by default.

Supplementary / experimental (explicitly non-core)
--------------------------------------------------

The core production route is WFGraph; the following modules are kept for
research/future work and are intentionally not part of the curated surface:

- `LogOS/Domain/ZFC/Supplementary/` (alternate routes, e.g. hereditarily-finite developments)
