<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS Naming Conventions

## Bulk/Boundary Pattern

LogOS uses a consistent naming pattern to distinguish bulk (full) and boundary (restricted) variants:

### Base Pattern

- **Bulk**: Base name (e.g., `Cosp`, `idC`, `RG`, `NF̂`)
- **Boundary**: Add `∂` suffix (e.g., `∂Cosp`, `id∂`, `RG∂`, `NF̂∂`)

Note: identifiers in this document are illustrative; not every example name appears verbatim in the current tree.

Interpretation (analogy):
some example identifiers (e.g. `RG`) use cross-domain terminology as motivation; this file only defines naming conventions, not theorems.

### Examples

| Bulk | Boundary | Description |
|------|----------|-------------|
| `Cosp` | `∂Cosp` | Cospan types |
| `idC` | `id∂` | Identity cospans |
| `compC` / `∘C` | `comp∂` / `∘∂` | Composition |
| `RG` | `RG∂` | Renormalization group |
| `NF̂` | `NF̂∂` | Normalization closure |
| `Flow` | `Flow∂` | World flows |
| `Sat-ω` | `Sat-ω∂` | Satisfaction |

### Preorders

Preorder relations follow the same pattern:

- **Bulk**: `≤C` (cospan preorder)
- **Boundary**: `≤∂` (boundary cospan preorder)
- **Weight**: `≤W`
- **Scale**: `≤S`
- **Time**: `≤T`
- **Entailment**: `≤Ent`

### Monoidal Operations

- **Bulk**: `⊕C`, `⊗C` (cospan operations)
- **Boundary**: `⊕∂`, `⊗∂` (boundary operations)
- **Weight**: `⊕W`, `⊗W`

### General Rule

When adding new operations or types that have both bulk and boundary variants:
1. Use the base name for the bulk version
2. Add `∂` suffix for the boundary version
3. Maintain consistency with existing naming

## Equality And Refinement Vocabulary

- `⊑`: refinement/order direction (primary kernel relation)
- `≈`: mutual refinement (`a ⊑ b` and `b ⊑ a`)
- `≡`: strict propositional equality (use only in strict/law-strengthened layers)
- `≃`: legacy alias surface; prefer `≈` or `≡` explicitly

### Context Relation Policy

- `≤ctx` is a context relation in `WorldH` by default.
- Preorder laws for `≤ctx` are supplied separately through
  `LogOS.Minimal.WorldLaws.For.CtxPreorder`.
