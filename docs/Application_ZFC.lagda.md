<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZFC Construction — LogOS (Axiom Ledger)

```agda
module docs.Application_ZFC where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.ZFC.All
import LogOS.Packs.ZFC.WFGraph

import LogOS.Domain.SetTheory.FormulaPack
import LogOS.Domain.SetTheory.FormulaFromDefinable
import LogOS.Domain.SetTheory.Pack
import LogOS.Domain.SetTheory.FullUpgradeFromDefinable
import LogOS.Logic.ZFC.Axioms
import LogOS.Logic.ZFC.Theory
```

This note is the single, publication-facing entrypoint for the set-theory story:
how the production LogOS library packages **ZF** (and optionally **ZFC**) as an
application pack **without touching the Kernel**.

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
  deduction (`LogOS.Logic.FOL.ND`). If you want *classical* ZFC, add a classical
  principle (e.g. excluded middle) explicitly as an extra axiom/rule; LogOS does
  not assume it silently.

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
  - `LogOS/Domain/SetTheory/FormulaPack.agda`
  - Definable → formula-pack bridge (makes the code-based interface operational):
    `LogOS/Domain/SetTheory/FormulaFromDefinable.agda`
  - Small derived conveniences for the formula-pack surface:
    `LogOS/Domain/SetTheory/FormulaDerived.agda`
  - `LogOS/Domain/SetTheory/Pack.agda`
  - Optional “full meta-level schema” upgrade (representability assumption):
    `LogOS/Domain/SetTheory/FullUpgradeFromDefinable.agda`
- Concrete model route (one worked semantics path):
  - `LogOS/Domain/ZFC/WFGraph/`
  - ZF(+Infinity) semantics, with ZFC = ZF + explicit AC witness
- Curated pack entrypoint:
  - `LogOS/Packs/ZFC/All.agda`
  - WFGraph pack quartets: `LogOS/Packs/ZFC/WFGraph.agda`
  - Minimal typechecked demo: `docs/ZFC_Demo.lagda.md`

## Quick import (namespaced)

```text
open import LogOS.Packs.ZFC.All as ZFC
```

## Reading guide (practical)

1. Start at `LogOS/Domain/ZFC/ARCHITECTURE.md` for the “hexagonal” module map.
2. The safe core only provides the kernel + closure machinery; all set-theoretic
   strength comes from explicit adapters/packs in `LogOS/Domain/SetTheory/`.
3. If you want a ZFC instance, look for the **single AC witness** and where it
   is threaded into the ZF pack (no hidden axioms).

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
| Choice (ZFC) | `ZFCAxiomsᶠ.AC` / `LogOS.Logic.ZFC.Axioms.FromZFCAxiomsᶠ.Choiceᶠ` | External witness / internalised sentence | ZFC is exposed as “ZF + AC witness”; the witness validates `Choiceᶠ` |

## Proof-theoretic touchpoint (optional)

`LogOS/Logic/ZFC/Axioms.agda` states the ZF axioms as **pure relational FOL**
sentences over `{∈,≈}` (plus code-indexed `Pred`/`Rel` symbols for the schemata),
and proves they are valid in any `ZFAxiomsᶠ` instance.

`LogOS/Logic/ZFC/Theory.agda` then packages these sentences into a FOL context
and instantiates the generic ND soundness theorem, giving an explicit
“derivations preserve validity” interpretation statement (plus a tiny derived
example theorem).

This interpretation statement is for the **intuitionistic** calculus. Any
classical reasoning is an *explicit* extra assumption on top of the ZF/ZFC
axiom context.
