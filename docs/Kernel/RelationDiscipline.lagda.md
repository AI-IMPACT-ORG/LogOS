<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Relation / Equality Discipline (Views + Pullbacks)

```agda
{-# OPTIONS --safe #-}
module docs.Kernel.RelationDiscipline where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; ObsEqOn; ObsLeOn)
open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.RelPreorder using (RelPreorder)
open import LogOS.Minimal.View
```

This page is the **notation governance** for relational symbols in LogOS. It is
intended to prevent “≈ drift” (using `≈` for things that are actually `≡`) and
to make the target semantics of any preorder/equality explicit.

Glyph meanings (global)
-----------------------

- `≡` is Agda propositional equality only.
- `⊑` is a preorder relation (the target preorder must be named).
- `≈` is **always** mutual refinement in some preorder: `x ≈ y` means `(x ⊑ y) × (y ⊑ x)` in that preorder.
- `≃` is pullback of `≡` along a view (strict equality of view images).
- `↔` is propositional equivalence only (pairs of maps), never “equality on objects”.

View-based discipline (one rule)
--------------------------------

To introduce a domain-specific preorder or equality on a type `X`, you must:

1. pick a target preorder `T` (order-theoretic or observational), and
2. provide an explicit **view** `V : View X T` (a map `μ : X → Con(T)`),
3. define the relation only as a pullback:
   - `x ⊑[ V ] y` (preorder pullback),
   - `x ≈[ V ] y` (mutual refinement in that preorder),
   - `x ≃[ V ] y` (strict pullback of `≡` along `μ`).

In code, these are the definitions exported by `LogOS/Minimal/View.agda`.

API rule of thumb (preorder-first)
----------------------------------

When designing *record interfaces*, treat a preorder/refinement as the primitive:

- prefer a primitive field `_⊑_` (or `_⇒_` in 2-categorical settings),
- define `_≈_` only as **derived notation**: `(x ⊑ y) × (y ⊑ x)`,
- do not make `_≈_` a primitive field of a record (it obscures the underlying preorder).

Ontology anchor
---------------

This discipline is treated as part of the **core ontology** of LogOS:
`≡` (strict, Agda) and `⊑` (refinement) are the primitive pillars; `≈`, `≃`, and
observational relations are *constructed* from them via views/pullbacks and
observational preorder builders.

As a practical cue, many core records provide both:
- the “two directions” presentation `(x ⊑ y) × (y ⊑ x)`, and
- an `≈`-shaped alias (mutual refinement) with the same content,
so downstream code can stay preorder-first while still reading like “equality
up to refinement”. Examples: `GTier.Th*-fixed≈` and `KernelShapeLaws.γ*-guard≈`.

Observational targets (satisfaction-induced)
--------------------------------------------

For a satisfaction predicate `Sat : P → X → Set`, the induced observational preorder is:

- `ObsPreorder Sat : RelPreorder _ _`, with relation `ObsLeOn Sat`.

The induced mutual refinement `Obs≈ Sat` is definitionally `≈` in that preorder.
The usual observational equality `ObsEqOn Sat` is logically equivalent to
two-way `ObsLeOn Sat` (and hence to `Obs≈ Sat`):

- `ObsEqOn↔Obs≈ Sat : ObsEqOn Sat x y ↔ Obs≈ Sat x y`.

Kernel tiers (canonical views)
------------------------------

Kernel-tier comparison relations should be named by their view:

- decoded meaning: view `decode` (`LogOS/Kernel/Eq.agda` provides `_≃K_` / `_≈K_`),
- observational meaning: view into `ObsPreorder` built from a tier’s satisfaction predicate,
- strict/logical meaning: use `_↔_` only at the proposition level.

For derived tier alignments (S/H/G/R) see `LogOS/Kernel/Tiers.agda`.
Canonical view registry (what to use/extend): `docs/Kernel/ViewRegistry.lagda.md`.

Convenience: `LogOS/Kernel/Tiers.agda` also exports view-named relations such as
`_⊑decode_` / `_≈decode_` / `_≃decode_` and observational `_⊑obs_` / `_≈obs_`.

Endomaps (boundary operators)
-----------------------------

The kernel endomap DSL treats boundary operators as endomaps `Endo K`.

- `_≤₂_` is **pointwise refinement** between endomaps.
- `_≈₂_` is **mutual refinement** between endomaps (two-way `_≤₂_`), and is the
  preferred “same effect” notion for endomaps.

Kernel morphisms (2-cells)
--------------------------

In the kernel 2-category developments (`LogOS/Kernel/Hom2Cat.agda` and
`LogOS/Kernel/Graded/Hom2Cat.agda`), 2-cells compare kernel morphisms by refinement.

There are two useful refinement relations:

- **Decode-quotiented refinement**: `f ⇒ g`, exported as `RefinesDecode f g`.
  This compares morphisms only on the decoded image of code:
  `∀ γ → decode (mapCode f γ) ⊑ decode (mapCode g γ)`.

- **Constraint-level refinement**: `Refines∂ f g`.
  This compares morphisms on *all* boundary constraints:
  `∀ c → map∂₁ f c ⊑ map∂₁ g c`.

The strong relation implies the quotiented one (`Refines∂→RefinesDecode`), by
restriction to decoded constraints.

Guidance:

- use `RefinesDecode`/`_⇒_` when you want presentation-independence on code
  (quotienting by `decode` is intentional), and
- use `Refines∂` when you need statements about all constraints, or when you
  want to avoid accidental weakness when `decode` is not dense.
