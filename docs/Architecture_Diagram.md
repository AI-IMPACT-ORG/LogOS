<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS architecture (one-page diagram)

This is a “blast-radius” view of the codebase: where meaning is defined, and what is allowed to depend on what.
Arrows indicate the allowed import direction: code in a lower box may import code in boxes above it.

```
┌───────────────────────────────┐
│ Host surface (allowlisted)     │
│ `LogOS/Host/**`                │
│ (only allowlisted files may    │
│  import `Agda.Primitive` /     │
│  `Agda.Builtin.*`)             │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Prelude (curated base)         │
│ `LogOS/Prelude.agda`           │
│ + `LogOS/Prelude/*`            │
│ (the host re-export bridge)    │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Core foundations               │
│ `LogOS/Base/*`, `LogOS/Syntax/*`│
│ `LogOS/Algebra/*`, `LogOS/Free/*`│
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Minimal interfaces             │
│ `LogOS/Minimal/*`              │
│ (preorders + lax laws)         │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Kernel + quantitative + compute │
│ `LogOS/Kernel/*`, `LogOS/QAdapters/*` │
│ `LogOS/Computation/*`          │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Boundary + ports + adapters    │
│ `LogOS/Boundary/*`, `LogOS/Ports/*` │
│ `LogOS/Adapters/*`             │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Theorems / meta-theory         │
│ `LogOS/Theorems/*`             │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Topic libraries (mature)       │
│ `LogOS/{ZFC,UniversalIR,Universality,Complexity,InfoTheory}/*` │
│ `LogOS/ObjectLogic/*`          │
│ (domain developments that are  │
│  safe to depend on from stable │
│  pack surfaces)                │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Experimental domains           │
│ `LogOS/Domain/*` (Opacity)     │
│ (stable roots must not reach   │
│  this namespace transitively)  │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Packs (curated entrypoints)    │
│ `LogOS/Packs/*`                │
│ (`packTrust` governs stability)│
└───────────────────────────────┘
```

Note: `LogOS/API/*` are core-only navigation/entry surfaces (no `LogOS.Domain.*` / `LogOS.Packs.*` imports) that sit
“beside” this stack; they re-export selected core layers without introducing application dependencies.

## Canonical navigation surfaces

- Architecture map (ports/adapters spine): `LogOS/API/Architecture.agda`
- Narrow API surfaces:
  - Foundations only: `LogOS/API/Foundation.agda`
  - Kernel work: `LogOS/API/Kernel.agda`
  - Canonical bridges (tier/repr/flow/limit): `LogOS/API/Bridges.agda`
  - Port-first downstream work: `LogOS/API/PortsAdapters.agda`
  - Minimal kernel-authoring bundle: `LogOS/API/Minimal.agda`

## Enforced invariants (CI/policy)

- Host import allowlist: `scripts/host_surface_check.sh`
- No direct `LogOS.Host.*` imports outside Prelude bridge: `scripts/host_import_check.sh`
- Layering (core must not import domains/packs/docs): `scripts/import_layer_check.sh`
- Stable surfaces must not import experimental: `scripts/stable_surface_no_experimental_imports_check.sh`
- Stable surfaces must not import `LogOS.Domain.*` directly: `scripts/stable_surface_no_domain_imports_check.sh`
- Stable surfaces must not import `LogOS.Theorems.Meta.Assumptions.*` directly: `scripts/stable_surface_no_meta_assumption_imports_check.sh`
- Stable surfaces must not reach `LogOS.Domain.*` or `LogOS.Theorems.Meta.Assumptions.*` transitively:
  `scripts/stable_surface_no_banned_transitive_imports_check.sh`
- Assumption ledger required when importing assumption packs: `scripts/assumptions_ledger_check.sh`
- Unsafe/options gates (`--safe`, no forbidden postulates, no dangerous pragmas): `scripts/unsafe_options_check.sh`, `scripts/postulate_policy_check.sh`, `scripts/safe_options_check.sh`, `scripts/dangerous_pragmas_check.sh`
  - Postulate allowlist/config: `scripts/postulate_allowlist.txt`
