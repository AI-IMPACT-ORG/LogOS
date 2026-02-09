<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Categorical Logic (Computational Trinity)

```agda
{-# OPTIONS --safe #-}
module docs.Views.CategoricalLogic where

-- Typechecked “view surface” for the categorical-logic presentation.
--
-- Keep this module intentionally lightweight: it should be importable alongside
-- other views/tests without introducing operator/name clashes.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.API.Views as Views
open Views.Kernels using (Kernel)

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = Views.ViewTheorems.For K
  open V.CategoricalLogic public

  private
    CodeThinCat-exists : _
    CodeThinCat-exists = CodeThinCat

    BoxFunctor-exists : _
    BoxFunctor-exists = BoxFunctor

    Kernel2Cat-exists : _
    Kernel2Cat-exists = Kernel2Cat

    Port2Cat-exists : _
    Port2Cat-exists = Port2Cat

    KernelCategory-exists : _
    KernelCategory-exists = KernelCategory

    prequantale-exists : _
    prequantale-exists = prequantale

    conAlg-exists : _
    conAlg-exists = conAlg

    projection-exists : _
    projection-exists = V.Projections.projection
```

Purpose
-------
This view presents a categorical-logic reading of LogOS: preorders are read as
thin categories, kernels and ports sit in a preorder-enriched 2-categorical
setting, and closure/stability operators are endomaps (modalities) living in
that order-enriched world.

Using refinement/inequalities rather than equality-level laws keeps irreversible structure visible; extensional upgrades are explicit assumptions.

The presentation is intentionally conservative: LogOS keeps category theory out
of the kernel signature, and provides it as a *view* over existing interfaces.

Interpretation (analogy):
this document is a derived presentation (“view”) over the same kernel interfaces;
it does not add logical power.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Notation (local)
----------------
- `c ⊑ d`: refinement/entailment in a preorder.
- `c ≈ d`: mutual refinement.
- `P ↔ Q`: satisfaction equivalence (paired implications).
- `x ≡ y`: propositional equality (`_≡_`), not judgmental equality.

Scope (formal)
--------------
- Parameter: `Kernel Sig Q`.
- Surface: `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CategoricalLogic`).

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Preorder as a thin category | `ConPreorder` (`LogOS/Minimal/Con.agda`) | “Category laws” are ops-level unless you assume proof-irrelevance. |
| Two-level preorder (carrier + relation universes) | `RelPreorder` (`LogOS/Minimal/RelPreorder.agda`) | Used when observational relations live in a larger universe than their carriers. |
| Monoidal structure on a preorder (ops vs laws) | `MonoidalOps` / `MonoidalLaws` (`LogOS/Minimal/Adjunction.agda`) | Ops are always available; laws are opt-in. |
| (Lax) adjunction / Galois connection | `LaxAdjunction`, `GaloisConnection` (`LogOS/Minimal/Adjunction.agda`) | Kernel uses the lax (inequality) form by default. |
| Frobenius reciprocity (lax) | `Frobenius.frobenius-ext≤` (`LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda`) | One-way inequality; avoids collapsing irreversible structure. |
| Beck–Chevalley (lax) | `LogOS/Theorems/CategoryTheory/BeckChevalley.agda` | Presented as commutation squares up to refinement. |
| Kernel morphisms as 1-cells, refinement as 2-cells | `LogOS/Kernel/Hom2Cat.agda`, `LogOS/Kernel/Graded/Hom2Cat.agda` (`KernelRelThin2Cat` / `GradedKernelRelThin2Cat`), `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda` | Locally preordered 2-category interface (canonical instance does not rely on carrier-level lifting). |
| Ports/adapters as a 2-category | `LogOS/Theorems/CategoryTheory/Port2Cat.agda` | “Presentation independence” is expressed as 2-cells (satisfaction equivalences `↔`). |
| Presentations as a thin 2-category | `LogOS/Ports/Semantic/Presentation2Cat.agda`, `LogOS/Theorems/CategoryTheory/Presentation2Ref2Cat.agda` | Kernel-independent: fixed satisfaction system, translations as 1-cells, refinement on meaning as 2-cells. |
| Processes as a thin 2-category | `LogOS/Computation/Process2Cat.agda`, `LogOS/Theorems/CategoryTheory/Process2Ref2Cat.agda` | Lax process morphisms as 1-cells, pointwise refinement of maps as 2-cells. |
| ωCPO maps as a thin 2-category | `LogOS/Theorems/Boundary/OmegaCPOMap2Cat.agda`, `LogOS/Theorems/CategoryTheory/OmegaCPO2Cat.agda` | “Domain-theory glue” packaged as 2-categorical bookkeeping (no new axioms). |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital prequantale in the finite-join sense (not complete) + time map. |

Core definitions (literature style)
-----------------------------------

**Definition (Thin category from a preorder).** Any preorder \((X, ⊑)\) gives a
thin-category façade:
- objects: elements of \(X\)
- morphisms: proofs of \(x ⊑ y\)
- identities/composition: reflexivity/transitivity.

LogOS uses this façade in an **ops-only** way unless you explicitly assume
proof-irrelevance (so that “category laws” become equalities of morphisms).

**Definition (Lax adjunction).** A “bulk↔boundary” interface is treated as a
lax adjunction: unit/counit are inequalities rather than equalities; the tight
(\(↔\)-law) form is packaged separately as `GaloisConnection`.

**Definition (Closure/nucleus).** A closure operator is `ClosureOp`:
monotone + inflationary + idempotent-lax. In LogOS this is the default strength
for “modalities” that model stabilisation/regularisation.

**Definition (Coherence squares).** Beck–Chevalley and Frobenius are presented
as commutation/interaction laws *up to refinement* (inequalities), preserving
the directed/irreversible character of refinement.

Assumptions (explicit)
----------------------
- Proof-irrelevance (or truncation) is needed if you want to treat refinement proofs as equalities of morphisms (literal thin categories).
- Antisymmetry is needed if you want to upgrade mutual refinement to propositional equality (`c ≈ d ⇒ c ≡ d`).
- Monoidal laws are opt-in: `MonoidalOps` is always available; add `MonoidalLaws`/`Monoidal` for textbook-strength monoidal structure.
- μ/limit-level results require explicit ωCPO/continuity bundles (they are not assumed by default).

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: preorder-as-thin-category structure, monoidal/adjunction patterns, and coherence theorems (Frobenius/Beck–Chevalley).
- Weaker/lax by default: 2-cells are refinement witnesses (directed/irreversible), and “laws” are ops-level unless you assume proof-irrelevance/antisymmetry.
- Added by ports/adapters: “presentation independence” is expressed as port-level translation/naturality rather than as a single privileged syntax.
- Assumption-scoped: any equality-level categorical structure is an explicit upgrade (e.g. `MonoidalLaws`, antisymmetry/proof-irrelevance packs).

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CategoricalLogic`):
  `CodeThinCat`, `BoxFunctor`, `Kernel2Cat`, `Port2Cat`, `KernelCategory`, `prequantale`, `conAlg`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- Additional 2-categorical packaging (kernel-independent bookkeeping, not specific to the CHL view):
  - thin 2-categories: `LogOS/Minimal/RelThin2Cat.agda` (general) and `LogOS/Minimal/Thin2Cat.agda` (same-universe specialization)
  - refinement-2-category wrapper core: `LogOS/Theorems/CategoryTheory/WrapperCore.agda` (`RelThin2Cat→Ref2CatCore` and `Thin2Cat→Ref2CatCore`)
  - presentations, processes, ωCPO maps: the modules listed in the dictionary above.

The prose below is explanatory; the statements above are the authoritative claims.

Micro-example (a 2-cell notion that is not equality)
----------------------------------------------------
At the boundary level, adapters between ports are unique **up to satisfaction**:
any two adapters \(A, A'\) between the same ports satisfy
\[
  \forall p,\varphi.\;\; \mathrm{Sat}(p, A(\varphi)) \;↔\; \mathrm{Sat}(p, A'(\varphi)).
\]
This is `adapter-confluent` in `LogOS/Ports/Semantic/Interoperability.agda` and
is the basic “2-cell” notion in the port 2-category (`Port2Cat`).

Pointers (no repetition)
------------------------
- Ports/adapters spine (definitions + uniqueness/naturality): `docs/DeepDive/Architecture_PortsAdapters.lagda.md`.
- Kernel/tier bookkeeping: `docs/LogOS_Core_Spec.lagda.md`.
- Categorical nuclei/sheaves leg: `docs/Views/Topos.lagda.md`.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- Multi-institution: `docs/Views/MultiInstitution.lagda.md`
- CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`
- Topos-shaped reading: `docs/Views/Topos.lagda.md`
