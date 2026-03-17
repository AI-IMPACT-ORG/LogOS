<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Assumptions ledger (v1.1)

This page lists the main **optional doctrines / axiom-like inputs** used by LogOS 1.1.

Key stance: LogOS tries hard to keep the kernel **weak and auditable**:

- core modules are checked under `--safe --no-libraries`
- `postulate` is forbidden by default (guarded by `scripts/check/postulate_policy_check.sh`)

When an “assumption” appears below, it is always an explicit record field or parameter: nothing is smuggled in
via unsafe flags or hidden axioms.

This ledger is intended to be the **authoritative index** of such optional doctrine/assumption records.
If you introduce a new assumption pack (typically a record named `*Assumptions`, `*Ledger`, or a cross-pack
meaning injection ledger), add it here.

## Optional doctrines in the core

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/LT/Flow.agda#GuardedClosure -->

### Guarded closure (Flow doctrine)

- Introduced: `LogOS/LT/Flow.agda` (`GuardedClosure`)
- Used by:
  - flow preservation: `LogOS/LT/HomFlow.agda`
  - flow-equipped component graph: `LogOS/LT/LOG/Flow2Cat.agda`, `LogOS/LT/LOG/ArchitectureFlowContract2Cat.agda`
  - boundary normalisation in iteration: `LogOS/LT/Iteration.agda` (`normTrace`, `run`)
  - stability + quote/eval interface: `LogOS/LT/Reflection.agda`
  - evaluator reflection universal property: `LogOS/LT/Theorems/EvaluatorReflection.agda`
  - KZ packaging: `LogOS/LT/AbstractKZ.agda`
- What it buys:
  - a compositional notion of “normalised/stabilised boundary spec”
  - a single lax-naturality inequality that can be demanded of adapters (`KernelHomFlow`)
  - a precise universal property for “reflecting” evaluators along a closure (maximal safe reflection)
- What it does *not* buy:
  - existence of any particular closure for your boundary (you must supply it)
  - least fixed points / μ-calculus semantics by default
  - operational “step semantics” correctness (that’s a separate modelling claim)

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/LT/Sup/FinSup.agda#FinSup -->

### Finite joins (optional algebra)

- Introduced: `LogOS/LT/Sup/FinSup.agda` (`FinSup`)
- Used by:
  - derived ω-sup summary `supω` (prefix-join construction): `LogOS/LT/Sup/SupOmega.agda`
  - boundary-level “run summary” (optional): `LogOS/LT/Iteration.agda` (`run`)
  - `QAdapter` scale boundaries: `LogOS/Ports/Valuation/ScaleBoundary.agda` (`ScaleBoundaryFinSup`)
- What it buys:
  - a canonical “finite aggregation” operator on boundary constraints (binary join + bottom)
- What it does *not* buy:
  - any infinitary completeness (no σ/ω supremum selector by default)

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/LT/Sup/AbstractSigmaDCPO.agda#SigmaDCPO -->

### σ-directed ω-suprema (optional infinitary completeness)

- Introduced: `LogOS/LT/Sup/AbstractSigmaDCPO.agda` (`SigmaDCPO`)
- Used by:
  - derived ω-sup summary `supω`: `LogOS/LT/Sup/SupOmega.agda`
  - boundary-level “run summary” (optional): `LogOS/LT/Iteration.agda` (`run`)
  - μ/ν-calculus fixed point utilities (optional, under σ-(co)continuity):
    `LogOS/LT/Sup/AbstractKleene.agda`, `LogOS/LT/Sup/AbstractCoKleene.agda`
- What it buys:
  - explicit suprema of **directed ω-families** (ℕ-indexed; upper bound + leastness as fields)
- What it does *not* buy:
  - full completeness (arbitrary joins), or proof-irrelevance/uniqueness of the chosen `supσ`

## Cross-pack semantics and port-level assumption packs

These are optional, explicitly parameterised “meaning injection” and “extra law” records that appear
throughout multiple packs and/or port stacks.

Neutral packaged context records such as
`DependentLocalSemantics` / `TwoStageDependentLocalSemantics`
and the universality/cost `Core` records now live outside the ledger on purpose:
they package shared context, not optional doctrine.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Ports/Universality/CTD/Ledger.agda#CTDLedger -->

### Church–Turing–Deutsch style universality (CTD ledger)

- Introduced: `LogOS/Ports/Universality/CTD/Ledger.agda` (`CTDLedger`)
- Used by:
  - concrete instance pack: `LogOS/Apps/Universality/CTD.agda`
  - tooling-loop normalisation corollary: `LogOS/LT/Theorems/Effectivisation.agda`
- What it buys:
  - an explicit, assumption-scoped universality claim: each system admits a **flow-preserving** simulation into a chosen universal kernel.
  - a derived “simulation commutes with normalisation” inequality (`normalize-simulate`).
- What it does *not* buy:
  - existence of a universal simulator kernel for your intended domain (you must supply it).
  - any operational correctness theorem for the simulator; CTD is a ledger interface, not a proof.
  - any resource/cost/fidelity story (those are separate ports/contracts).

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Ports/AbstractLandauer/Ledger.agda#LandauerAssumptions -->

### Landauer-style cost assumptions (optional cost layer)

- Introduced: `LogOS/Ports/AbstractLandauer/Ledger.agda` (`LandauerAssumptions`, `LandauerMonotone`)
- Used by:
  - law-port totalisation (explicit cost bounds on adapters): `LogOS/Ports/AbstractLandauer2Cat.agda`
  - general causal + cost stack: `LogOS/Ports/AbstractCausalLandauer2Cat.agda`
  - causal prequantum entrypoint: `LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda`
- What it buys:
  - an explicit grading/cost assignment on morphisms, with identity neutral up to observation (`≈`) and submultiplicativity as a refinement inequality (`⊑`).
  - a compositional way to carry cost bounds as an independent decoration layer (without making cost part of kernel refinement).
- What it does *not* buy:
  - a claim that the chosen cost function corresponds to thermodynamic entropy/energy (that interpretation is external).
  - additivity/multiplicativity as equality (only the refinement direction is assumed).

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Ports/PreQuantum/Purification.agda#PurificationAssumptions -->

### Purification / dilation existence (prequantum / CQM-style assumption pack)

- Introduced: `LogOS/Ports/PreQuantum/Purification.agda` (`PurificationAssumptions`, `PurificationWitness`)
- Used by:
  - law-port totalisation (Σ-decoration with explicit witnesses): `LogOS/Ports/PreQuantum/Purification2Cat.agda`
  - causal prequantum entrypoint over causal + cost: `LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda`
- What it buys:
  - a per-morphism “dilation exists” witness: each `f` admits a chosen `u : A → B ⊗ E` such that discarding `E` recovers `f` up to observation (`≈`).
  - an explicit identity/composition witness calculus for the displayed purification port, so witness bookkeeping is supplied rather than silently recomputed after composition.
- What it does *not* buy:
  - a CPM/environment construction or any quotienting principle (those would be stronger, separate developments).
  - uniqueness/canonicity of dilations; witnesses are designer-chosen data.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda#CausalPreQuantumAssumptions -->

### Causal + Landauer + purification (causal prequantum entrypoint)

- Introduced: `LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda` (`CausalPreQuantumAssumptions`)
- Used by:
  - the causal prequantum stacked law-port 2-category and its forgetful functor (same module).
- What it buys:
  - a single record bundling independent extra-law layers over the causal physical category:
    cost bounds (`LandauerAssumptions`) + monoidal/discard structure + purification witnesses.
  - a uniform “stack ports, then Σ-totalise” construction that keeps refinement inherited from the base.
- What it does *not* buy:
  - any “unitarity” axiom or physical completeness claim; this is deliberately weaker and refinement-first.
  - any change to what counts as refinement between underlying adapters (displayed evidence is ignored by `_⊑_` on total morphisms).

## Application-level assumptions (ZFC pack)

The ZFC pack’s canonical “model surface” is **stack-first and first-order**:
Separation/Replacement are treated as *formula-coded* upgrades (`ZFCStackFO`),
and the primary stack-first route factors through an explicit reification
doctrine on the predicate boundary (up to a chosen guarded closure `Flow`).

### ZFC upgrade and assumption packs

- Generated index: `docs/Generated/ZFC_Upgrade_Index.md`
- Policy rule: if a new ZFC record ends in `Assumptions`, `Ledger`, or `Upgrade`, add it here and to
  `scripts/zfc_upgrade_manifest.tsv`.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=docs/Core/Meta/Assumptions_Ledger.md#zfc-upgrade-packages -->
#### Upgrade packages {#zfc-upgrade-packages}

- `EmptyOrElemUpgrade`
- `MemWellFoundedUpgrade`
- `FoundationUpgrade`
- `SeparationUpgrade`
- `ReplacementUpgrade`
- `ChoiceUpgrade`
- `SeparationFOUpgrade`
- `ReplacementFOUpgrade`

<!-- CLAIM-STAMP: ASSUMPTION | anchor=docs/Core/Meta/Assumptions_Ledger.md#zfc-upgrade-assumptions -->
#### Assumption packages {#zfc-upgrade-assumptions}

- `BaseAssumptions`
- `StructuralAssumptions`
- `FoundationAssumptions`
- `CoKleeneInfinityAssumptions`

<!-- CLAIM-STAMP: ASSUMPTION | anchor=docs/Core/Meta/Assumptions_Ledger.md#zfc-upgrade-ledgers -->
#### Ledgers {#zfc-upgrade-ledgers}

- `SetMMZFLedger`

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/AsymptoticReification/ReificationPort.agda#PredicateReification -->

### Predicate reification (boundary doctrine)

- Introduced: `LogOS/Apps/ZFC/Stack/AsymptoticReification/ReificationPort.agda` (`PredicateReification`)
- Used by:
  - `LogOS/Apps/ZFC/Stack/AsymptoticReification.agda` (derive constructor profiles and FO upgrades *once stability is assumed*)
  - `LogOS/Apps/ZFC/Stack/ReifiedTower.agda` (curated packaging into `ZFCStackFO`)
- What it buys:
  - a disciplined “collapse only at the boundary” interface:
    reify a predicate into a set whose membership matches `Flow`-observation,
    but only for *admitted* predicates (an explicit `Reifiable` gate).
- What it does *not* buy:
  - stability of any particular predicate family (that is stated separately),
  - any form of unbounded comprehension: admitting `Reifiable` for a predicate family is explicit data,
    and extra “reifiable families” appear only via additional ledger fields (e.g. FO upgrades),
  - ω/Infinity/Foundation/Choice (those remain explicit ledger fields).

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/AsymptoticReification/ReificationPort.agda#TotalPredicateReification -->

### Total predicate reification (explicitly stronger / experimental)

- Introduced: `LogOS/Apps/ZFC/Stack/AsymptoticReification/ReificationPort.agda` (`TotalPredicateReification`)
- Used by:
  - `LogOS/Apps/ZFC/Stack/ReificationAsQuotePort.agda` (bridge surface: `QuotePort` corresponds to the *total* wrapper)
- What it buys:
  - the old, unrestricted shape `reify : Predicate → SetU` with a pointwise membership law.
- What it does *not* buy (and why it is separated out):
  - any safety by default: combined with `Flow = id` this amounts to unbounded comprehension and admits
    Russell-style diagonalisation; keep it as an explicit, opt-in experiment surface.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/AsymptoticReification/StagedAdmissibility.agda#StagedPredicateReification -->

### Staged predicate reification (late-collapse admissibility ledger)

- Introduced: `LogOS/Apps/ZFC/Stack/AsymptoticReification/StagedAdmissibility.agda` (`StagedPredicateReification`)
- Used by:
  - concrete ZFC reification instances that want a primitive stage/rank-indexed admissibility surface and a canonical
    forgetful map to the ordinary restricted reification ledger
- What it buys:
  - a stage/rank-indexed admissibility family `ReifiableAt i P`, with monotone transport along an LT-native stage preorder (`stageCP : ConPreorder ... ...`)
  - stage-indexed reification data `reifyAt` / `mem-reifyAt↔` as the primitive late-collapse interface
  - a canonical forgetful map to the restricted-by-default `PredicateReification` interface used by `ReifiedTower`
  - explicit conversion boundaries:
    `restricted→staged`, `total→staged`, and `staged→total` only when a separate stage-totality witness is supplied
  - a natural place to encode cumulative-hierarchy style "admitted by stage/rank" discipline without changing downstream ZFC layers
- What it does *not* buy:
  - an actual stage semantics or cumulative hierarchy by itself: the stage order and admissibility family remain explicit data
  - any weakening of the warning about total reification: `staged→total` is still an explicit strong wrapper, not a free consequence
  - proofs that particular FO predicate families are admitted; those remain explicit witnesses supplied by the concrete instance

The first concrete instance now lives in
`LogOS/Apps/ZFC/Models/IterativeSetTree/StagedReification.agda`. It turns the
iterative-set-tree rank into a stage order and uses "represented by a tree at
that rank" as admissibility. Two sharp assumptions remain explicit there:

- `Extensionalityᵛ`: because the raw tree carrier uses intensional membership,
  pair-style constructor laws need a way to collapse membership-derived `_≈_`
  back to definitional equality.
- `PowersetStructureᵛ`: because the raw iterative tree alone does not provide
  full powerset closure in the same universe.

The next same-stage packaging rung lives in
`LogOS/Apps/ZFC/Models/IterativeSetTree/LateCollapse.agda`. It keeps the same
architecture discipline, but the curated semantic entrypoint is
now the typed hierarchy surface in
`LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`, which re-exports:

- the stage-local assumption types
  `ExtensionalCollapseᵛ`, `StageAssumptionsᵛ`,
- the coherent hierarchy-section type
  `HierarchySectionᵛ`,
- the namespaced canonical surfaces
  `Canonical.ForLevel`, `Canonical.BridgeForLevel`,
- the namespaced optional completion adapter
  `Completion.ForLevel`.

The underlying architecture is:

- the generic stack/proof-side late-collapse packaging now lives in
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/LateCollapseTower.agda`,
- canonical same-stage rung data and canonical successor transport now live in
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/Hierarchy.agda`,
- canonical successor bridges now live in
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/SuccessorBridge.agda`,
  which now also carries the generic theorem-facing successor-stage
  Separation/Replacement set and schema names,
- same-stage completion decorations now live in
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/CompletionLayer.agda`,
- canonical bridge slices plus completion aliases now live in
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/HierarchySlice.agda`,
- the iterative-tree canonical slice lives in
  `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda`,
- the theorem-facing canonical bridge facade lives in
  `LogOS/Apps/ZFC/Models/IterativeSetTree/CanonicalBridge.agda`,
- the iterative-tree optional completion adapter lives in
  `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchyCompletion.agda`,
- the generic composer now also has a staged entrypoint (`ForStaged`), so the
  iterative-tree path consumes staged FO witnesses directly instead of
  hand-collapsing back to a restricted-only interface first,
- constructor and FO stability are then derived automatically because the
  concrete reifier uses `idClosure`,
- `ω`/Infinity are now supplied internally by
  `LogOS/Apps/ZFC/Models/IterativeSetTree/HierarchyInfinity.agda`, using the
  raw tree `ω` together with the staged core and extensionality of the
  presentation layer,
- well-founded closure is derived automatically because every iterative set tree
  is accessible under intensional membership,
- the remaining non-forced surfaces stay explicit: the hierarchy ledger
  (`Extensionalityᵛ`, `PowersetStructureᵛ`), the LT-aligned small Separation
  classifier port, and the generic structural assumption bundle containing
  Choice and the `EmptyOrElemUpgrade` chooser used by the Foundation upgrade.

The FO closure is more LOG-g aligned now, but still honest about the last gap:

- `LogOS/Apps/ZFC/Models/IterativeSetTree/RankBoundedFO.agda` packages a
  `FORepresentabilityᵛ` record and computes the stage component of FO witnesses
  from the rank of the generated tree itself, instantiating the generic
  local-presentability assembly in
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/LocalPresentationFO.agda`,
- Separation is no longer assumed as an arbitrary representing set: it is
  generated from a small classifier on the existing children of the tree via
  `LogOS/Apps/ZFC/Models/IterativeSetTree/GeneratedSubtree.agda`, which now
  exports strict/equality-shaped presentation data that is lifted into the
  canonical congruence-aware contract from
  `LogOS/LT/Presentation/GeneratedSubobject/Core.agda`; the
  remaining app-level seam is now just the small-classifier witness itself,
- Replacement is also no longer assumed as an arbitrary representing set: it is
  generated from the functionality witness via
  `LogOS/Apps/ZFC/Models/IterativeSetTree/GeneratedImage.agda`, which now
  exports strict image data lifted into the canonical congruence-aware
  contract from `LogOS/LT/Presentation/GeneratedImage.agda`,
- the iterative late-collapse layer therefore keeps `foRepresentability`, but
  that port now carries only LT-level small classifiers for Separation rather
  than arbitrary FO representing sets.

What does *not* disappear is the constructive structural boundary:

- the remaining small Separation classifier is still needed because the raw tree
  carrier does not force full formula truth down to the child-index level:
  `evalFormula` lives one universe above the child indices,
- `EmptyOrElemUpgrade` is still needed because a raw iterative tree
  `sup I f` does not canonically provide either an inhabitant of `I` or a proof
  that `I` is empty,
- `Choice` is still explicit because nothing in the raw presentation/staged
  hierarchy generates a global choice function.

There is now a clean successor-stage escape from that remaining FO seam:

- `LogOS/Apps/ZFC/Stack/AsymptoticReification/CrossStageReificationPort.agda`
  packages predicate reification from a source set context into a larger target
  context,
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/CrossStageFOFromReification.agda`
  lifts Separation/Replacement views across that stage boundary,
- `LogOS/Apps/ZFC/Models/IterativeSetTree/SuccessorTruthLift.agda` instantiates
  the pattern for iterative trees,
- `LogOS/Apps/ZFC/Models/IterativeSetTree/Hierarchy.agda` packages one
  coherent family of stage ledgers across levels,
- `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda` cuts a
  successor slice from one hierarchy section and keeps the canonical bridge
  separate from same-stage local completion,
- `LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda` is the small curated
  semantic entrypoint for downstream consumers.

Pedantically: this does **not** claim that the raw iterative-tree stage is now
closed under same-stage FO reification. It states the sharper and correct fact:
the remaining raw-stage Separation classifier disappears one stage up.
Pedantically again: the canonical bridge is available from the hierarchy
section alone, while same-stage proof models still require explicit local
completion data at the chosen rung.

Pedantically once more: the repeated presentation steps are now typed
refinement-first.
`LogOS/Apps/ZFC/Stack/AsymptoticReification/LocalPresentationFO.agda` and
`LogOS/Apps/ZFC/Models/IterativeSetTree/SuccessorTruthLift.agda` factor
generated images and formula transport through refinement-aware interfaces
first; extensional collapse is used there only as an explicit adapter back to
raw presentation equalities.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/AsymptoticReification/CoreFromReification.agda#CoreStability -->

### Core stability (constructor predicates)

- Introduced: `LogOS/Apps/ZFC/Stack/AsymptoticReification/CoreFromReification.agda` (`CoreStability`)
- Used by:
  - `LogOS/Apps/ZFC/Stack/ReifiedTower.agda` (build a `ZFStackBase` from reified core/powerset)
- What it buys:
  - stability obligations for the *constructor-defining* predicates (Pair/Union/Powerset),
    so the corresponding membership laws can be stated without visible `Flow`.
- What it does *not* buy:
  - any “derivation” of ZF(C): it is an assumption boundary for a chosen reification doctrine.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/AsymptoticReification/FOFromReification.agda#FOStability -->

### FO stability (definable predicates)

- Introduced: `LogOS/Apps/ZFC/Stack/AsymptoticReification/FOFromReification.agda` (`FOStability`)
- Used by:
  - `LogOS/Apps/ZFC/Stack/ReifiedTower.agda` (derive formula-coded Separation/Replacement upgrades)
- What it buys:
  - stability obligations for the FO-definable predicates needed to package
    textbook-style *formula-coded* Separation/Replacement (`ZFCStackFO`).
- What it does *not* buy:
  - any higher-order comprehension; only what is stated for explicit `Formula` codes.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/AsymptoticInfinityUpgrade.agda#CoKleeneInfinityAssumptionsᵣ -->

### ν / CoKleene infinity upgrade (optional)

- Introduced: `LogOS/Apps/ZFC/Stack/AsymptoticInfinityUpgrade.agda` (`CoKleeneInfinityAssumptionsᵣ`)
- Used by:
  - `LogOS/Apps/ZFC/Stack/ReifiedTower.agda` (`ReifiedZFCFOCoKleene`)
- What it buys:
  - an alternative route to ω/Infinity: derive an ω-object and its membership law
    from the ν fixed-point spine, assuming σ-directed completeness and σ-co-continuity.
- What it does *not* buy:
  - ω/Infinity without explicit assumptions: the required completeness/continuity inputs are explicit fields.

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/ProfileTower/Core.agda#ChoiceUpgrade -->

### Choice transformer upgrade (ZFC refinement)

- Introduced: `LogOS/Apps/ZFC/Stack/ProfileTower/Core.agda` (`ChoiceUpgrade`)
- Used by:
  - `LogOS/Apps/ZFC/Stack/ReifiedTower.agda` (the `choiceUpgrade` ledger field)
- What it buys:
  - an explicit choice transformer (a `View` plus a `ChoiceFunctionOn` law) refining ZF to ZFC.
- What it does *not* buy:
  - global classical choice as a kernel principle (it remains app-level structure).

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Apps/ZFC/Stack/FoundationUpgradeFO.agda#FoundationAssumptions -->

### Foundation upgrade (FO) assumptions

- Introduced: `LogOS/Apps/ZFC/Stack/FoundationUpgradeFO.agda` (`FoundationAssumptions`)
- Used by:
  - the curated tower packaging: `LogOS/Apps/ZFC/Stack/ReifiedTower.agda`
- What it buys:
  - a clean separation between the implication-form Foundation law (derived from well-founded descent) and the disjunctive form
    (derived once an explicit “empty or element chooser” is installed).
  - an explicit upgrade step (`foundationUpgrade`) that does not strengthen the kernel; it packages the extra obligations.
- What it does *not* buy:
  - Foundation without explicit assumptions: both choice-style and well-foundedness inputs are explicit record fields.

## Pack-level coherence principles (distributed boundaries)

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/Ports/Globalise.agda#Globalise -->

### Globalisation (optional global coherence for function boundaries)

- Introduced: `LogOS/Ports/Globalise.agda` (`DependentGlobalise` (canonical); uniform constant-family wrapper: `Globalise`)
- Used by:
  - currently no checked core pack depends on it
  - available as an explicit late strictification port for downstream distributed-boundary packs
- What it buys:
  - a clean separation between pointwise “local theorems” and strict global `≡` coherence,
    so you can treat global equalities as an explicit antisymmetry-based strictification step taken late.
- What it does *not* buy:
  - any of the pointwise mathematics (you still have to supply `decode-mapCodeAt`),
  - any particular notion of global coherence beyond the one you explicitly package,
  - function extensionality in the kernel (it stays out of core).
