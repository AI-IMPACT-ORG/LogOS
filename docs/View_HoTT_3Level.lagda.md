<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS as a 3-Level HoTT-Style System (S / H / G)

```agda
module docs.View_HoTT_3Level where

open import LogOS.Docs.Views.View_HoTT_3Level public
```

This note explains the intended “3-level HoTT” reading of the LogOS architecture.
It is deliberately explicit about what is *implemented* vs what is an *optional axiom*
you may add on top.

Key points:

- LogOS is built as a **three-tier** system (S/H/G) with **explicit coherences**
  between the tiers.
- The core does **not** assume “equality = equivalence” globally; it uses preorders and
  explicit bi-implications. This is the host-minimal, transport-friendly default.
- “Univalence-like” principles appear as **opt-in upgrades** (e.g. antisymmetry / faithfulness),
  allowing movement between an extensional (set-like) and a homotopical (equivalence-like) reading
  without changing the kernel.

Three levels in the implementation
----------------------------------
LogOS names the tiers:

1) **S — Strict**
   - A formula carrier `Fml` and a satisfaction predicate `Sat_S`.
   - Entailment is packaged in `StrictTruth.StrictLayer` (`LogOS/Minimal/Truth.agda`).

2) **H — Homotypical**
   - A satisfaction predicate `Sat_H` for boundary constraints.
   - An invariance/projector `Inv_H` (a nucleus/closure operator) that captures “truth up to
     invariance” in the target model.
   - This tier is designed so theorems are phrased in terms of *structure* and *transport*
     rather than definitional equalities.

3) **G — Guarded**
   - A closure operator on boundary constraints (a nucleus/projector). In the Kernel code this
     step is named `Flow` (field of `GuardedTruth.GuardedClosure`).
   - A distinguished (preorder) fixed point `Th*` (global stable truth). With optional antisymmetry
     (and, for ω-limit results, `OmegaCPO`/continuity structure), this upgrades to a genuine least
     fixed point for limit constructions.
   - This tier is the “stability/communication” layer: local truths become globally stable via
     the closure step.

The coherence laws between tiers are **fields of the Kernel record** (`LogOS/Kernel.agda`):

- `coh-LH` connects strict S-truth to H-truth via `TransH : Fml → Con∂` using a *bi-implication*
  (`_↔_`), not a definitional equality.
- `sat-coh` connects world-indexed H-truth to boundary-indexed H-truth via `bnd`.

Why this is “HoTT-style” (and not just “3 modules”)
---------------------------------------------------
Two design choices are key:

### 1) Equivalences are first-class (and equality is not forced)
Across the repo, “coherence” is phrased as `_↔_` (pairs of functions) and order inequalities,
not definitional equalities. This mirrors the HoTT discipline:

- identify structure via equivalence/transport,
- treat equality (judgmental or propositional) as *additional structure*, not the default.

In code, this appears as:
- preorders as the default notion of “constraint order” (`LogOS/Minimal/Con.agda`),
- coherence records using `_↔_` from `LogOS/Syntax/Prop.agda`.

### 2) Modal/closure structure is explicit (Flow as a modality)
The guarded tier packages a closure/nucleus `Flow`. Fixed points of a nucleus are the
standard categorical semantics of a modality (monotone, inflationary, idempotent‑lax endomap),
and under antisymmetry this upgrades to equality-level idempotence; LogOS makes this explicit
at the boundary logic level.

This is what powers:
- “local truth vs global truth” theorems (fixed point transport),
- diagonal/Rice/Tarski meta-theorems phrased at decode level,
- physics/complexity “resource bottleneck” interfaces phrased as closure-stability claims.

Where “univalence” fits (what exists today)
-------------------------------------------
LogOS already contains the **slots** where univalence-like upgrades live:

### Univalence for posets / preorders (0-truncated univalence)
The core is preorder-based. If you assume antisymmetry, then “mutual entailment” becomes equality.
This is the poset analogue of univalence at truncation level 0:

> if `c ⊑ d` and `d ⊑ c`, then `c ≡ d`.

In the library this is exactly the optional “upgrade from preorder to partial order”
provided by `PartialOrder` in `LogOS/Minimal/Con.agda`.

### Faithfulness of embeddings (univalence-like reflection principle)
In operator/bridge packs (e.g. Hilbert–Pólya), a common “univalence-like” assumption is that an
embedding reflects equality (no information loss). This is packaged explicitly as a record
field (e.g. `EmbedFaithful` in the HP interface).

These are not global axioms; they are **local packs** you choose to assume when you want a
fully extensional reading.

What is *not* claimed by default
------------------------------------
This 1.0 library does *not* claim “full HoTT” in the sense of:

- a built-in univalence axiom for all types,
- higher inductive types,
- a univalent universe hierarchy.

Instead, the repo is engineered so that:

1) the core stays small and host-minimal,
2) equivalence-first reasoning is the default (via `_↔_`, projectors, and transport),
3) univalence-like principles can be added as *explicit, scoped* assumption packs
   where the application warrants it (e.g. collapsing observational equivalence classes).

How to use this in writing
--------------------------
If you want a precise, publication-friendly sentence:

> LogOS is a three-tier logic (S/H/G) whose coherences are expressed by equivalences and closure
> operators; univalence-like extensionality principles are optional, explicitly packaged upgrades
> (antisymmetry/faithfulness), rather than hidden global axioms.

Cross references
----------------
- Kernel definition and coherence fields: `LogOS/Kernel.agda`
- Minimal tier interfaces: `LogOS/Minimal/Truth.agda`
- Preorders/partial orders: `LogOS/Minimal/Con.agda`
- `_↔_` and negation discipline: `LogOS/Syntax/Prop.agda`
