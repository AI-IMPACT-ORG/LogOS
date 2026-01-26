<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Opacity (Observability Ledgers; Conditional Application)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.Opacity where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.Opacity.Experimental.Surface

-- Identifier sync guards (claim-heavy): these names are referenced in the prose.
import LogOS.Packs.Opacity.Experimental.Applications.GRH as GRHApp
open GRHApp.Guarded using (GRH; mkPack)
open import LogOS.Packs.Opacity.Experimental.Core using (VacuityGuards)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)
open import LogOS.Theorems.Meta.LimitPublicisation using (TruthK→Pr)
open import LogOS.Theorems.Meta.SpectralSeparationOutput using (separation-output-not-total)
open import LogOS.Theorems.Meta.BudgetedSeparationOutput using (budgeted-diagonal-witness)
```

This note is the single, publication-facing entrypoint for the **opacity / observability**
strand in the production library.

Trust level: **experimental**. This pack is under evaluation and should be
considered less stable than the rest of the repository. It is a conditional
application ledger; use its claims only with the stated vacuity guards and
explicit axioms.

LogOS does **not** claim to prove classical analytic number theory. Instead it:

1. makes the dependency graph explicit (an *axiom ledger*), and
2. proves clean **strategy-barrier theorems** about what can and cannot be made
   totally observable inside reflective systems.

Even without new analytic proofs, these GRH/RH-shaped ledgers are valuable as
reverse mathematics: they expose the minimum “coverage/adequacy” hypotheses
needed to close the classical statement.

> TL;DR: Opacity is the “observability ledger” layer: it defines a canonical
> observable/communicable fragment `Pr` from the kernel, proves no‑total‑oracle
> barrier theorems for extensional observers, and packages analytic number theory
> statements (e.g. GRH/RH) as **conditional** ledgers with explicit assumptions.

## At a glance

What you get (and where to look):

- **Kernel-derived observability:** `Pr` / “limit publicisation” (`LogOS/Theorems/Meta/CommunicableTruth.agda`, `LogOS/Theorems/Meta/LimitPublicisation.agda`)
- **GRH/RH as an axiom ledger:** `LogOS/Domain/Opacity/ZetaTruthLedger.agda` (with vacuity guards via `LogOS/Domain/Opacity/Meaningfulness.agda`)
- **Kernel-driven assumption weakenings:** stable truth ⇒ observable (`TruthK→Pr`), meet-limit/cofinal scheduling, Hasse–Yoneda probe coverage
- **Barrier theorems (“no total oracle”):** `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` (+ budgeted variants)

```text
W-pos (truth/positivity on tests)
  └─ Pr(W-pos)    -- observable/communicable fragment (kernel-derived)
       └─ analytic bridge (Weil probe lemma) / operator bridge (HP) / nucleus separation
            └─ GRH_Without_Vacuity_Guards  (+ explicit vacuity guards when packaging GRH)
```

## Observational indistinguishability (simulators/adapters)

Opacity is also used as a *semantic indistinguishability* interface:

- `LogOS/Domain/Opacity/Indistinguishability.agda` — observational equivalence
  on boundary ports and preservation by port adapters (simulators), plus the
  ObsEqF‑functorial lemma `simulator-preserves-ObsEqF`.
- `LogOS/Domain/Opacity/TelemetryInvariant.agda` — telemetry traces are stable
  under observational equivalence (observation-only discipline).

Guarded vs guardless application claim (canonical vs raw):

- Canonical claim object: `LogOS/Domain/Opacity/GRHLedger.agda` (guards + packaged GRH/RH claim with explicit vacuity guards).
- Guardless predicate: `GRH_Without_Vacuity_Guards` from `ZerosPack` (no vacuity guards).
- Naming rule: guardless theorems are prefixed `GRH_Without_Vacuity_Guards-`.

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
- Full GRH requires an explicit **probe coverage / adequacy**
  hypothesis (a choice-like axiom for the probe family).

The “observable sector / superselection” form is packaged in:

- `LogOS/Domain/Opacity/ObservableSector.agda`

### Kernel-driven strengthenings (weaken the observer axiom)

The baseline Weil ledger needs a “probe is observable”/coverage hypothesis to go
from the weak criterion to full GRH. When the truth predicates you care about are
already **decode-extensional** (up to `_≈K_`) and **kernel-stable** (stable under the kernel’s
closure modality, e.g. `Box` / `BoxAt`), the kernel can discharge much
of that burden:

- Stable truth is observable: `TruthK→Pr` (`LogOS/Theorems/Meta/LimitPublicisation.agda`)
- `Pr` can be read as “stable under `Box ∘ Body`” (since `FlowCode` and `Box (Body _)` coincide after `decode`):
  `Pr↔Pr-BoxBody` (`LogOS/Theorems/Meta/CommunicableTruth.agda`)
- Stable-truth ledger (single predicate): `LogOS/Domain/Opacity/AccessibleWeilLedger.agda`
- Stable meet-limit bridge: `LogOS/Domain/Opacity/AccessibleWeilMeetLimitBridgeStable.agda`
- Cofinal schedule variant (ω-chain style): `LogOS/Domain/Opacity/AccessibleWeilMeetLimitBridgeStableCofinal.agda`
- ζ-facing wrapper (meet-limit): `LogOS/Domain/Opacity/ZetaAccessibleMeetLimitLedgerStable.agda`
- ζ-facing wrapper (coverage via Hasse + Yoneda transport): `LogOS/Domain/Opacity/ZetaHasseYonedaLedger.agda`

For one-line “systems” entrypoints (operator, nucleus/forcing, and the kernel-strengthened
Weil routes), see:

- `LogOS/Domain/Opacity/Applications/GRH/Systems.agda`

## Forcing/nucleus generalization (Flow is a restriction)

The primary abstraction is **forcing-style truth separation**: close probes with
an arbitrary nucleus/closure operator on the boundary preorder, then derive the
global “on-line” predicate from that closure. This is the most general interface:
this is *not* the ZFC forcing machinery, only the abstract closure-operator pattern.

- `LogOS/Domain/Opacity/TruthSeparationForcing.agda` (`ForcingTruthSeparation`)

The Flow-based story is a **specialization** with `J = Flow`:

- `LogOS/Domain/Opacity/TruthSeparation.agda` (`FlowTruthSeparation`)

Use the forcing form when you want external nuclei (e.g. local operators,
coverage-induced closures, or model-specific projectors); use the Flow form when
you want the kernel’s canonical closure step.

## Relation to literature

This pack is designed to sit on top of several established strands, while
keeping their assumptions explicit:

- **Explicit-formula/Weil criteria:** the GRH ledger mirrors standard analytic
  number theory reductions, but treats them as pack fields rather than derived
  theorems.
- **Diagonalization and no-total-oracle results:** the opacity theorems are the
  usual recursion-theoretic barrier stated for observable probes, with explicit
  decode-extensionality (up to `_≈K_`) and budget parameters.
- **Forcing/sheaf-style closures (interpretation):** the nucleus-based truth
  separation has the same closure-operator shape as forcing or sheafification,
  with `Flow` as a canonical kernel instance.

## GRH with vacuity guards

Some generic GRH/RH statements can be made trivially true by degenerate
instantiations (e.g. `NontrivialZero` empty, or `OnLine ≡ ⊤`). The production
library therefore provides vacuity guards:

- `LogOS/Domain/Opacity/Meaningfulness.agda`

For a packaged GRH claim object with guards,
use:

- Canonical guarded surface: `LogOS/Domain/Opacity/GRHLedger.agda`
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
via `_⊔s_` (more allowance) and model sequential composition via `_·_`.

### Recommended Scale instantiation (typechecked snippet)

For any kernel `K : Kernel Sig Q`, the canonical budget carrier is the quantale
scale `QAdapter.Scale Q` with its order `_≤s_` (and in graded settings this is
the same carrier used for grades):

```agda
module Budgeted-Scale-Snippet where
  open import LogOS.Prelude
  open import LogOS.Base.Signature using (LogOSSignature)
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.Kernel using (Kernel)
  import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO

  module _
    {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (O : SSO.SpectralSeparationOutput K)
    where
    open QAdapter Q
    module GB = SSO.GeneralB O

    -- Budgets/witness costs in the quantale scale (no decidability required):
    module _ (CB : GB.WitnessCostB Scale) where
      module G = GB.General Scale _≤s_ CB
```

Interpretation: for any budget policy `Bnd : Code → Scale`, `G.no-total-within-budget Bnd …`
says there is no decode-extensional (up to decoded observational equality, `_≈K_`) oracle that is total *and* always produces a witness
whose grade is ≤ `Bnd γ`. This aligns directly with graded kernels by taking budgets in `Scale`.

## HP (Hilbert–Pólya) opacity theorem (no total spectral oracle)

For HP-style operator routes, the production library includes a formal
“no total extensional certificate oracle” theorem:

- Generic barrier: `LogOS/Theorems/Meta/SpectralSeparationOutput.agda`
- HP-specialized instance: `LogOS/Domain/Opacity/NumberTheory/HP/Opacity.agda`
- Budgeted/graded strengthening (within-budget opacity): `LogOS/Domain/Opacity/NumberTheory/HP/Opacity.agda` (module `Budgeted`),
  a thin wrapper over `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda` (ℕ budgets) and
  `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` (`GeneralB.WitnessCostB` for abstract budgets).

This is the precise statement behind:

> a fully explicit, total “spectral certificate oracle” for the global object is blocked

more precisely: given a decode-extensional (up to decoded observational equality, `_≈K_`) oracle surface (`SpectralSeparationOutput`) and a
Tarski-style truth diagonal (`TruthDiagonal`), diagonalization forces an explicit code where the
oracle must return `undefined`. In particular, no such oracle can be total.

## Bibliography pointers (not exhaustive)

- B. Riemann (1859), "Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse".
- A. Weil (1952), "Sur les formules explicites de la theorie des nombres premiers".
- H. M. Edwards (1974), "Riemann's Zeta Function".
- A. Tarski (1936), "Der Wahrheitsbegriff in den formalisierten Sprachen".
- K. Godel (1931), "Uber formal unentscheidbare Satze der Principia Mathematica und verwandter Systeme I".
- P. J. Cohen (1963), "The Independence of the Continuum Hypothesis".

## Curated import (namespaced)

```text
open import LogOS.Packs.Opacity.Experimental.Surface as Opacity
import LogOS.Packs.Opacity.Experimental.Applications.GRH as GRHApp
module GRHSystems = GRHApp.Guardless.Systems
open import LogOS.Packs.Opacity.Experimental.Core as OpacityCore
module HPOpacity = OpacityCore.HPOpacity
```

`Opacity` provides the ledgers and system wrappers; `HPOpacity` provides the
HP opacity theorem and its generic corollaries.
