<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Meta — Safety Spine (Design Choice → Architecture → Paradox Gates)

```agda
{-# OPTIONS --safe #-}
module docs.Meta_Safety where

-- Sync guard: anchor the safety spine paths.
import LogOS.Theorems.Meta.Safety.All
```

This note makes one claim precise:

> The hexagonal architecture is a derivable consequence of the *safety design choice*:
> LogOS assumes only the kernel interface and requires all paradox‑enabling
> structure (truth predicates, provability, diagonalization, comprehension, etc.)
> to be introduced explicitly as *assumption packs*.

Audit rule: the available paradoxes are exactly those whose gate/assumption packs you import; importing only a `Kernel` instance keeps those gates closed.

### Design choice (core)

The design choice is recorded as a tiny pack:

- `LogOS/Theorems/Meta/Safety/DesignChoice.agda`

It contains only a `Kernel` instance. There are **no** additional internal
paradox-enabling predicates/operations (e.g. truth over code, provability,
diagonalization, comprehension) unless the user imports explicit assumption
packs.

### Architecture as consequence

From that minimal choice, the boundary/port/interlingua spine is derivable:

- `LogOS/Theorems/Meta/Safety/ArchitectureFromSafety.agda`

Key consequences (formalized):
- Boundary I/O exists (`BoundaryIO`): a derived boundary-facing satisfaction
  interface (built from the kernel’s H-tier truth via `sat-coh`).
- Canonical ports exist (boundary port + code port).
- Canonical translation is forced (`Interlingua` / `PortAdapter` uniqueness).
- Bootstrapping is an adapter equivalence `Adapter≈` between the canonical ports (`bootstrap-iso`).
- Guarded truth provides a distinguished fixed-point witness (`Th*` and code
  witness `γ*`); leastness/μ-induction requires explicit ωCPO/continuity
  assumptions. (`guard-decode` is the Guard↔Flow coherence law.)

This is *not* an extra axiom: it is a consequence of the kernel laws.

Note on naming: internal helper lemmas in `ArchitectureFromSafety` carry a
`-core` suffix, while the record fields keep the clean, paper‑facing names
(`bootstrap`, `bootstrap-unique`, `guard-decode`, `decode∘encode`). This keeps the
record interface stable without shadowing core definitions.

### Paradox gates (why the classics don’t apply by default)

The safety list is encoded as explicit “gates”:

- `LogOS/Theorems/Meta/Safety/AvoidanceList.agda`

For paper-facing summaries, the matrix record packages the architecture proof
and all gate types in one place:

- `LogOS/Theorems/Meta/Safety/Matrix.agda` (`SafetyMatrix`)

Each paradox is parameterized by the structure it requires. Examples:

- **Russell / Burali–Forti** require a membership theory + comprehension.
- **Liar / Tarski / Yablo** require a truth predicate + diagonalization
  (`TruthDiagonal`), which is not supplied by the kernel.
- **Gödel / Löb** require a provability predicate + implication rules +
  diagonalization (`Provability`, `ProvabilityOps`, `ImpRules`, `Diagonalization`).
- **Curry** requires provability + implication + diagonalization (explicit gate).
- **Berry** requires a definability predicate (explicit gate).
- **Reflection paradoxes** require a self‑reference pack (`QuoteSubst`), which is
  explicitly optional.
- **Explosion** requires an explicit ex‑falso rule (not in the kernel).

Tightened consequences (non‑vacuity):
- `Curry.fixedpoint` constructs an explicit self‑referential `γ` with
  `⊢ (γ → (γ → ⊥))` and `⊢ ((γ → ⊥) → γ)` once the Curry gate is supplied.
- `ExplosionConsequences` shows that `⊢ ⊥` collapses provability to “everything”
  and that non‑trivial provability implies `¬ ⊢ ⊥`.

The meta‑theory does not “solve” paradoxes; it isolates them structurally. You
only get the paradoxes you explicitly opt into by importing the necessary gates.
