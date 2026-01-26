<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS architecture (one-page diagram)

This is a “blast-radius” view of the codebase: where meaning is defined, and what is allowed to depend on what.

```
┌───────────────────────────────┐
│ Host surface (namespaced)      │
│ `LogOS/Host/*`                 │
│ (only place allowed to import  │
│  `Agda.Primitive` /            │
│  `Agda.Builtin.*`)             │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Prelude (curated base)         │
│ `LogOS/Prelude.agda`           │
│ + `LogOS/Prelude/*`            │
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
│ Kernel integration             │
│ `LogOS/Kernel/*`               │
│ (S/H/G + Code, reindexing, …)  │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Ports + adapters spine         │
│ `LogOS/Ports/*`, `LogOS/Adapters/*` │
│ + boundary I/O `LogOS/Boundary/*`   │
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
│ Domain developments            │
│ `LogOS/Domain/*`               │
│ (e.g. ZFC / Opacity / IR / …)  │
└───────────────┬───────────────┘
                │
                ▼
┌───────────────────────────────┐
│ Packs (curated entrypoints)    │
│ `LogOS/Packs/*`                │
│ (`packTrust` governs stability)│
└───────────────────────────────┘
```

## Canonical navigation surfaces

- Architecture map (ports/adapters spine): `LogOS/API/Architecture.agda`
- Narrow API surfaces:
  - Foundations only: `LogOS/API/Foundation.agda`
  - Kernel work: `LogOS/API/Kernel.agda`
  - Port-first downstream work: `LogOS/API/PortsAdapters.agda`
  - Batteries-included bundle: `LogOS/API/Minimal.agda`

## Enforced invariants (CI/policy)

- Host import allowlist: `scripts/host_surface_check.sh`
- No direct `LogOS.Host.*` imports outside Prelude bridge: `scripts/host_import_check.sh`
- Layering (core must not import domains/packs/docs): `scripts/import_layer_check.sh`
- Stable surfaces must not import experimental: `scripts/stable_surface_no_experimental_imports_check.sh`
- “Honesty” gates (`--safe`, no forbidden postulates, no dangerous pragmas): `scripts/honesty_check.sh`, `scripts/postulate_policy_check.sh`, `scripts/safe_options_check.sh`, `scripts/dangerous_pragmas_check.sh`
