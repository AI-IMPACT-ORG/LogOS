<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: boundaries as locales (observation geometry)

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Boundaries_As_AbstractLocales where

import LogOS.API.LT
```

This repo treats **observation** as primary: a boundary preorder is the space of *observable constraints/specs*,
and refinement is induced/preserved by explicit views.

A useful (optional) mental model for human consumption is to read boundaries geometrically:

- boundaries behave like **point-free spaces** (locales), and
- closure/doctrine (`Flow`) behaves like a **nucleus-style closure** selecting an “effective” subspace.

Nothing in the LT kernel assumes this structure; it is a *reading* and a target for optional ports/packs.

## Polarity: opens live in the opposite preorder

In LogOS, `c ⊑ d` is read as “`d` refines/entails `c`” (the right side is stronger).
On public-facing explanatory surfaces, the same judgement may be written `c ≼ d`.
If you want the standard topology/locale convention “opens ordered by inclusion”, work in the opposite preorder:

- `Opp (bnd K)` (see `LogOS/LT/ConPreorder.agda` and `LogOS/LT/PredicateReindexing.agda`).

This polarity flip is already used in the Σ-totalisation / predicate-reindexing reading of contracts.

## Flow as nucleus-style closure, stability as sublocale

At the boundary level, `GuardedClosure` is a KZ-style modality (monotone + inflationary + lax-idempotent):

- `LogOS/LT/Flow.agda` (`GuardedClosure`)
- `LogOS/LT/AbstractKZ.agda` (`KZModality`)

The induced reflection into stable points is already mechanised:

- `LogOS/LT/Reflection.agda` (`quot`, `evalm`, `quot⊣evalm`)

Locale reading:

- a nucleus-style closure is a KZ-style modality on opens;
- the fixed/stable opens form a sublocale-style reflective subspace;
- `quot ⊣ evalm` can be read as the sublocale reflection.

If you additionally supply finite meets and prove meet preservation, this becomes a literal (preorder-level) nucleus:

- `LogOS/LT/AbstractNucleus.agda` (`Nucleus`)

If you further equip a boundary with frame/Heyting/Boolean operations, you recover the standard locale/nucleus story.
Without that extra algebra, the KZ modality still gives the “effective semantics = stable specs” picture.

Optional σ-structure note:

- if a boundary has finite joins (`FinSup`) and σ-directed ω-suprema (`SigmaDCPO`)
  (see `LogOS/LT/Sup/FinSup.agda`, `LogOS/LT/Sup/AbstractSigmaDCPO.agda`),
  you can also talk about σ/ω-locale style completeness and continuity assumptions **without** assuming
  arbitrary global suprema selectors.

## Galois connections induce closures (nucleus-style) (standard order-theoretic alignment)

In locale theory, nuclei are (meet-preserving) closure operators; a common way to present a closure is as the
composite `R ∘ L` of a Galois connection/adjunction `L ⊣ R`.
In LogOS terms this is not extra kernel structure: it is a *derived* guarded closure (nucleus-style).

Code anchor (v1.1 core, minimal): `LogOS/LT/Theorems/AbstractGaloisConnection.agda`.

Terminology note: in residuation-style settings, `R` is often called the *residual* of `L`. LogOS keeps the
adjunction data explicit; residual-language is available as a thin vocabulary wrapper:
`LogOS/Ports/Residuals.agda`.

## Where “points” come from (two consistent choices)

There are two ways to talk about points/models:

1. **Intrinsic spectrum (locale-theoretic):** define points as appropriate morphisms out of the locale of opens
   (e.g. prime filters, frame maps into a truth object). This needs additional structure/assumptions and is
   intentionally not in the kernel.

2. **Kernel-relative model space (repository-local, immediate):** points are `Code K`.
   A constraint `c : Con (bnd K)` defines the “basic open” of models that satisfy it:
   `⟦c⟧ ≔ { γ : Code K | c ≼ decode γ }`.
  This is satisfaction (`LogOS/LT/Contracts.agda`: `K ⊨ γ [ c ]`).

The second is the default PL/tooling reading: the boundary generates a topology-like observational structure on code.

## Lawvere-style interpretation (structural alignment, not analogy)

This boundary/observation stance is aligned with the Lawvere / institution-fragment / predicate-reindexing tradition:

- `LogOS/LT/InstitutionFragment.agda`: kernels induce an institution fragment (signatures = kernels, sentences = boundary constraints,
  models = code, satisfaction = `c ≼ decode γ`, translations = `KernelHom`).
- `LogOS/LT/PredicateReindexing.agda`: contracts are a Σ-totalisation (category-of-elements-style; refinement inherited from the base, displayed evidence ignored) over the (opposite)
  boundary fiber.

In that sense, “observation geometry” is not an extra theory: it is a compact way to read existing infrastructure.

## Downstream use (why we care)

Once you adopt a shared distributed-semantics discipline (e.g. a fixed locality index and shared `Flow`):

- adapters become continuity-like structure (they preserve observation and, optionally, `Flow`),
- `Flow` becomes “causal/effective closure” (nucleus-style), and stable specs are the effective opens,
- granularity becomes a first-class translation problem (see `docs/Patterns/HowTo/HowTo_Build_Logic_Transformer_Architecture.lagda.md`).

This is also the structural skeleton of “one boundary, many boundary realisations” programs:

- generic surface: `LogOS/Ports/Realisations/DependentStack.agda`
- generic reading: multiple local observation families can share one distributed
  boundary, and transports between them preserve observation (and, optionally,
  `Flow`) without changing the kernel core.
  Code anchors: `LogOS/Ports/Realisations/DependentStack.agda`,
  `LogOS/Ports/PhysicalTransformers.agda`.

Anchors:

- shared distributed-semantics discipline: `docs/Patterns/Shared_Distributed_Semantics.lagda.md`
- local-to-global causality tooling loop (canonical, dependent): `LogOS/Ports/PhysicalTransformers.agda`
