<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Opacity (Observability Ledgers; GRH as a Conditional Application)

```agda
module docs.Application_Opacity where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Models.Opacity.Core
import LogOS.Domain.Opacity.ZetaTruthLedger
import LogOS.Domain.Opacity.WeilCriterionLedger
import LogOS.Domain.Opacity.ObservableSector
import LogOS.Domain.Opacity.Meaningfulness
import LogOS.Domain.Opacity.GRH
import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts
import LogOS.Domain.Opacity.NumberTheory.HP.Opacity
import LogOS.Theorems.Meta.SpectralSeparationOutput
import LogOS.Theorems.Meta.BudgetedSeparationOutput
import LogOS.Theorems.Meta.BudgetedTruthPositivity
import LogOS.Domain.Opacity.Applications.GRH
```

This note is the single, publication-facing entrypoint for the **opacity / observability**
strand in the production library.

LogOS does **not** claim to prove classical analytic number theory. Instead it:

1. makes the dependency graph explicit (an *axiom ledger*), and
2. proves clean **strategy-barrier theorems** about what can and cannot be made
   totally observable inside reflective systems.

Guarded vs guardless GRH (canonical vs raw):

- Canonical claim object: `LogOS/Domain/Opacity/GRH.agda` (guards + GRH proof).
- Guardless predicate: `GRH_Without_Vacuity_Guards` from `ZerosPack` (no vacuity guards).
- Naming rule: guardless theorems are prefixed `GRH_Without_Vacuity_Guards_*`.

## ζ vs ξ (completed zeta) is explicit in the interface

The facts pack is `LogOS/Domain/Opacity/NumberTheory/LFunction/RiemannFacts.agda`. It distinguishes:

- **ζ** (uncompleted): the `L` field of `LFunction` (Dirichlet series / Euler product region),
- **ξ/Ξ** (completed): `Lambda = Gamma · L`,
- **nontrivial zeros**: `XiZero s` (zeros of the completed object) plus `InStrip s`,
- **critical line**: `OnLine s` (in the facts-pack adapter, `Re s ≡ 1/2`).

This is an *axiom ledger* distinction (fields/predicates in a pack), not a claim that the
analytic properties of ζ/ξ are derived inside the core logic.

Terminology note: the code uses the identifier `GRH` as the generic “all nontrivial
zeros lie on the critical line” predicate for an abstract spectral adapter. For the
Riemann ζ/ξ instance this is the classical **RH**; for Dirichlet/automorphic families
it matches the usual **GRH** naming.

## The “axiom ledger” route (GRH as application)

The clean one-line entrypoint is:

- `LogOS/Domain/Opacity/ZetaTruthLedger.agda`

It separates three ingredients:

1. **ζ/ξ facts** (textbook-shaped, schematic): `RiemannFacts`
2. **observer-facing truth**: `TruthPositivity` (positivity only for `Observable` tests)
3. **analytic clause**: a Weil/explicit-formula criterion that turns probe-positivity into `OnLine`

The crucial split is in `LogOS/Domain/Opacity/WeilCriterionLedger.agda`:

- The **weak criterion** yields only “GRH on observable probes”.
- Full GRH requires an explicit **probe coverage / observational completeness**
  hypothesis (a choice-like axiom for the probe family).

The “observable sector / superselection” form is packaged in:

- `LogOS/Domain/Opacity/ObservableSector.agda`

## GRH with vacuity guards

Some generic GRH/RH statements can be made trivially true by degenerate
instantiations (e.g. `NontrivialZero` empty, or `OnLine ≡ ⊤`). The production
library therefore provides vacuity guards:

- `LogOS/Domain/Opacity/Meaningfulness.agda`

For a packaged GRH claim object with guards,
use:

- Canonical guarded surface: `LogOS/Domain/Opacity/GRH.agda`
  (re-exports `LogOS/Domain/Opacity/GRH_Vacuity_Guards.agda`).
- Raw predicate alias (no guards): `GRH_Without_Vacuity_Guards`

## Quantitative upgrade (budgeted observability)

The same opacity story can be stated **quantitatively** by replacing “observable” with
“observable within budget `b`”. Two generic, kernel-agnostic interfaces support this:

- Budgeted truth positivity: `LogOS/Theorems/Meta/BudgetedTruthPositivity.agda`
  (e.g. instantiate budgets as proof lengths or time-bounded Kt-style witnesses).
- Budgeted certificate/oracle opacity: `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda`
  (for each fixed budget, diagonalization forces an explicit input where the budgeted
  observer returns `undefined`).

Graded-kernel note: the same story can be instantiated with *non-ℕ* budgets.
Both meta modules now include generalized forms where budgets live in an abstract
carrier `B` with an order. In particular, when working with `GradedKernel`, you
can take `B` to be `QAdapter.Scale Q` and the budget order to be `_≤s_`, so
“observable within budget” aligns with the kernel’s quantale-grade resource model.
Because `Scale` is a (finite‑join) quantale, you can also combine budget policies
via `_⊔s_` (alternative allowances) and model sequential composition via `_·_`.

### Recommended graded instantiation (snippet)

For a graded kernel `K : GradedKernel Sig Q`, the canonical budget carrier is the
quantale scale `QAdapter.Scale Q` with its order `_≤s_`:

```text
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Theorems.Meta.BudgetedSeparationOutput as BSO

-- Given any extensional partial-output oracle `O : SpectralSeparationOutput (ToKernel K)`,
-- define “within budget” directly in the quantale scale.
module _ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : GradedKernel Sig Q) where
  open QAdapter Q
  open BSO.For (GradedKernel.ToKernel K) O C
  module G = General Scale _≤s_ CB
```

Interpretation: for any budget policy `Bnd : Code → Scale`, `G.no-total-within-budget Bnd …`
says there is no decode-extensional oracle that is total *and* always produces a witness
whose grade is ≤ `Bnd γ`. This is the direct “graded kernel” version of budgeted opacity.

## HP (Hilbert–Pólya) opacity theorem (no total spectral oracle)

For HP-style operator routes, the production library includes a formal
“no total extensional certificate oracle” theorem:

- Generic barrier: `LogOS/Theorems/Meta/SpectralSeparationOutput.agda`
- HP-specialized instance: `LogOS/Domain/Opacity/NumberTheory/HP/Opacity.agda`

This is the precise statement behind:

> a fully explicit, total “spectral certificate oracle” for the global object is blocked

more precisely: given a decode-extensional oracle surface (`SpectralSeparationOutput`) and a
Tarski-style truth diagonal (`TruthDiagonal`), diagonalization forces an explicit code where the
oracle must return `undefined`. In particular, no such oracle can be total.

## Curated import (namespaced)

```text
open import LogOS.Models.Opacity.Core as Opacity
open import LogOS.Domain.Opacity.NumberTheory.HP.Opacity as HPOpacity
```

`Opacity` provides the ledgers and system wrappers; `HPOpacity` provides the
HP opacity theorem and its generic corollaries.
