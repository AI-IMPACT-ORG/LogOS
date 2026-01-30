<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZFC Construction — LogOS (Axiom Ledger)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.ZFC where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.ZFC.Surface
```

This note is the single, publication-facing entrypoint for the set-theory story:
how the production LogOS library packages **ZF** (and optionally **ZFC**) as an
application pack **without touching the Kernel**.

Trust level: **stable** (lock surface: `LogOS/Packs/ZFC/Surface.agda`).

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

The key design choice is the same as in Metamath and most proof assistants:
**schemata range over codes/formulas**, not over arbitrary Agda predicates.
So “what is observable/usable” is the fragment that can be named and interpreted.

## What is meant by “ZFC” here

- **ZF**: the first-order ZF schemata are exposed as explicit records over a
  formula/code interface plus an interpretation/satisfaction relation.
- **ZFC**: Choice is not derived; it is a separate explicit witness, just as in
  mainstream formalizations. In addition, LogOS internalises Choice as a single
  first-order sentence (`Choiceᶠ`) and proves it valid in any `ZFCAxiomsᶠ`
  model that carries such a witness.
- **Logic strength**: the shipped proof system is **intuitionistic** natural
  deduction (`LogOS.ObjectLogic.FOL.ND`). If you want *classical* ZFC, add a classical
  principle (e.g. excluded middle) explicitly as an extra axiom/rule; LogOS does
  not assume it silently. (Convenience bundle: `LogOS/ObjectLogic/FOL/AllClassical.agda`.)

Two distinct layers are used throughout the library:

- **Object/first-order layer** (`ZFAxiomsᶠ`, `ZFCAxiomsᶠ`): Separation/Replacement
  range over **codes** with explicit semantics (`Pred`/`Rel`). This is the
  publication-facing “first-order ZF(C) mechanised” interface.
- **Meta convenience layer** (`ZFAxioms`, `ZFCAxioms`): Separation/Replacement
  range over **Agda predicates/functions**. This is strictly stronger unless you
  supply explicit representability assumptions, which LogOS does via
  `FullUpgradeFromDefinable`.

## Where the construction lives

- Set-theory interfaces (schemata over formulas/codes):
  - `LogOS/Domain/ZFC/SetTheory/FormulaPack.agda`
  - Definable → formula-pack bridge (makes the code-based interface operational):
    `LogOS/Domain/ZFC/SetTheory/FormulaFromDefinable.agda`
  - Small derived conveniences for the formula-pack surface:
    `LogOS/Domain/ZFC/SetTheory/FormulaDerived.agda`
  - Canonical schema name aliases (Extensionality/Separation/Replacement/etc.):
    `LogOS/Domain/ZFC/SetTheory/SchemaTheorems.agda`
  - `LogOS/Domain/ZFC/SetTheory/Pack.agda`
  - Optional “full meta-level schema” upgrade (representability assumption):
    `LogOS/Domain/ZFC/SetTheory/FullUpgradeFromDefinable.agda`
- Forcing-like closure surface (boundary Flow as a nucleus):
  - `LogOS/Domain/ZFC/SetTheory/Dsl.agda` (ZFDsl; membership respects the boundary `Flow`)
  - `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda` (uses `μFlow` when `OmegaCPO` + `FiniteFirst` are supplied)
- Concrete model route (one worked semantics path):
  - `LogOS/Domain/ZFC/WFGraph/`
  - ZF(+Infinity) semantics, with ZFC = ZF + explicit AC witness
  - Mostowski-style collapse (fold ∘ unfold transport of membership):
    `LogOS/Domain/ZFC/WFGraph/Mostowski.agda`
  - Formula-coded variant (codes are genuine first-order formulas, `decode` = extension):
    - `LogOS/Domain/ZFC/WFGraph/FormulaCode.agda`
    - `LogOS/Domain/ZFC/WFGraph/FormulaKernel.agda`
    - `LogOS/Domain/ZFC/WFGraph/FormulaPack.agda` (surface: `LogOS/Domain/ZFC/WFGraph/Surface.agda` → `FormulaCoded W`)
- Curated pack entrypoint:
  - `LogOS/Packs/ZFC/Surface.agda` (umbrella: `LogOS/Packs/ZFC/All.agda`)
  - WFGraph pack quartets: `LogOS/Packs/ZFC/WFGraph.agda`
  - Minimal typechecked demo: `docs/DeepDive/ZFC_Demo.lagda.md`

## Relation to literature

The ZF/ZFC pack follows standard formalization patterns, but keeps the logic
kernel unchanged:

- **Schema over codes:** like Metamath or other proof assistants, separation and
  replacement range over formula codes with explicit semantics; the formula-pack
  layer makes this a first-class interface.
- **Representability upgrades:** the `FullUpgradeFromDefinable` bridge matches
  the common move from definable predicates to code-based schemata, but keeps
  that move explicit as an assumption.
- **Forcing-style closures:** the boundary `Flow` layer is the LogOS analog of
  closure operators used in forcing or sheaf semantics, phrased in a kernel-native
  way (this is *not* the ZFC forcing machinery; only the abstract closure-operator pattern).
  Completing this to textbook ZFC forcing would be an additional layer. Present a forcing
  site (preorder+coverage, or complete Boolean algebra) as a boundary presentation; define the
  object-language forcing satisfaction `p ⊩ φ` as such a presentation/port; and prove a
  forcing theorem/truth lemma for that semantics, with genericity packaged as an explicit
  witness meeting the chosen cover/dense conditions.
  (Ports/presentations: `LogOS/Boundary/Port.agda`, and canonical translation: `LogOS/Ports/Semantic/Interlingua.agda`.)

## Quick import (namespaced)

```text
open import LogOS.Packs.ZFC.Surface as ZFC
```

## Reading guide (practical)

1. Start at `LogOS/Domain/ZFC/ARCHITECTURE.md` for the “hexagonal” module map.
2. The safe core only provides the kernel + closure machinery; all set-theoretic
   strength comes from explicit adapters/packs in `LogOS/Domain/ZFC/SetTheory/`.
3. If you want a ZFC instance, look for the **single AC witness** and where it
   is threaded into the ZF pack (no hidden axioms).

## Forcing-like closure (Flow / μFlow)

LogOS models “forcing-style closure” at the boundary as a closure operator
(monotone + inflationary + idempotent‑lax; sometimes called a “nucleus” in this repo).
The ZF DSL makes this explicit: membership respects the global step `Flow`, and the
boundary realiser is required to be stable under `Flow`.

If a model supplies `OmegaCPO` + `FiniteFirst` for the boundary preorder, then
`StageToCH-fromCH-μFlow` replaces the distinguished witness `Th*` (historical name: `Th⋆K`) with the **Kleene μ**
of `Flow`. This gives a least pre-fixed-point interpretation of the infinity stage in the
boundary preorder, without adding any axioms to the kernel.

## Axiom ledger (WFGraph route)

This table is intentionally blunt: every set-theoretic “strength” is either
**derived** from the WFGraph kernel route, or **assumed as an explicit structure**.

| ZF(C) component | Interface field / sentence | WFGraph route status | Notes |
| --- | --- | --- | --- |
| Extensionality | `ZFAxiomsᶠ.extensionality` / `ZFAxioms.extensionality` | Assumed | Via `ExtensionalityStructure` on the carrier graph |
| Empty | `ZFAxiomsᶠ.empty` / `ZFAxioms.empty` | Derived | From `SupStructure` (`supN`) over an empty index |
| Pairing | `ZFAxiomsᶠ.pairing` / `ZFAxioms.pairing` | Derived | `supN` over a 2-element index |
| Union | `ZFAxiomsᶠ.union` / `ZFAxioms.union` | Derived | `supN` over “members of members” |
| Successor / 0 | `ZFAxiomsᶠ.zeroS`, `ZFAxiomsᶠ.succ` (+ specs) | Derived | `zeroS-empty` and `mem-succ↔` are part of the pack contract |
| Powerset | `ZFAxiomsᶠ.powerset` / `ZFAxioms.powerset` | Assumed | Via `PowersetStructure` (kept explicitly modular) |
| Infinity | `ZFAxiomsᶠ.infinity` | Derived | ω is built as a concrete `supN` of iterated successors |
| Separation (schema) | `ZFAxiomsᶠ.separationᶠ` | Derived | Schema ranges over `Code` with `Pred` semantics |
| Replacement (schema) | `ZFAxiomsᶠ.replacementᶠ` | Derived | Requires `FunctionalRel` premise (single-valuedness up to `≈`) |
| Foundation | `ZFAxiomsᶠ.foundation` | Assumed | Via `FoundationStructure` on the carrier graph |
| Choice (ZFC) | `ZFCAxiomsᶠ.AC` / `LogOS.ObjectLogic.ZFC.Axioms.FromZFCAxiomsᶠ.Choiceᶠ` | External witness / internalised sentence | ZFC is exposed as “ZF + AC witness”; the witness validates `Choiceᶠ` |

## Proof-theoretic touchpoint (optional)

`LogOS/ObjectLogic/ZFC/Axioms.agda` states the ZF axioms as **pure relational FOL**
sentences over `{∈,≈}` (plus code-indexed schema symbols, separated as predicate-codes vs relation-codes),
and proves they are valid in any `ZFAxiomsᶠ` instance.

`LogOS/ObjectLogic/ZFC/Theory.agda` then packages these sentences into a FOL context
and instantiates the generic ND soundness theorem, giving an explicit
“derivations preserve validity” interpretation statement (plus a tiny derived
example theorem).

This interpretation statement is for the **intuitionistic** calculus. Any
classical reasoning is an *explicit* extra assumption on top of the ZF/ZFC
axiom context.

As of the current library version, the proof layer has two complementary surfaces:

- **Finite-instance contexts** (`BaseCtx`, `ZFctx`, `ZFCtx`): convenient when you want a
  small “axioms as list” context and a single soundness lemma (`sound-BaseCtx`, `sound-ZFctx`,
  `sound-BaseCtxZFC`, `sound-ZFCtx`).
- **Schema-native axioms** (`ZFAx`, `ZFCAx`): avoids enumerating Separation/Replacement instances.
  You prove a sentence as a derivation from the axiom predicate (`DerivZF`, `DerivZFC`) and interpret it
  with `sound-ZF` / `sound-ZFC`. The parametric variants `sound-ZF+` / `sound-ZFC+` express the
  “ZFC + additional axioms” story: add an extra axiom predicate and supply its validity in the model.

For an explicit classical add-on, see `LogOS/ObjectLogic/FOL/Classical.agda` (e.g. `DNE`/`LEM` as extra axioms).

## Bibliography pointers (not exhaustive)

- E. Zermelo (1908), "Untersuchungen uber die Grundlagen der Mengenlehre I".
- A. Fraenkel (1922), "Zu den Grundlagen der Cantor-Zermeloschen Mengenlehre".
- T. Skolem (1922), "Einige Bemerkungen zur axiomatischen Begrundung der Mengenlehre".
- K. Godel (1940), "The Consistency of the Continuum Hypothesis".
- P. J. Cohen (1963), "The Independence of the Continuum Hypothesis".
