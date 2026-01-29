<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Topos-Shaped Reading (Nuclei, Sheaves, Realizability Orientation)

```agda
{-# OPTIONS --safe #-}
module docs.Views.Topos where

-- Typechecked “view surface” for a conservative topos-shaped reading.
--
-- This document intentionally stays at the level of nuclei/local-operators and
-- Beck–Chevalley/Frobenius-shaped coherence, because those are what the core
-- LogOS kernel actually supports without importing a full topos semantics.

open import LogOS.Prelude public

open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary; MonoMap)
open import LogOS.Minimal.Adjunction using (MonoidalOps; LaxMonoidalAdjunction)

import LogOS.Theorems.CategoryTheory.AdjunctionMonads as AdjMon
import LogOS.Theorems.CategoryTheory.BeckChevalley as BC
import LogOS.Theorems.Reflection.ForcingSheaves as ForcingSheaves
import LogOS.Theorems.Reflection.NucleusMu as NucleusMu

module Quotes
  {ℓ : Level}
  {BB : BulkBoundary ℓ}
  {MBulk : MonoidalOps (BulkBoundary.bulk BB)}
  {MBnd  : MonoidalOps (BulkBoundary.bnd  BB)}
  (Holo : LaxMonoidalAdjunction BB MBulk MBnd)
  (mono-ext : MonoMap
    (BulkBoundary.bnd BB)
    (BulkBoundary.bulk BB)
    (LaxMonoidalAdjunction.ext Holo))
  (mono-bnd : MonoMap
    (BulkBoundary.bulk BB)
    (BulkBoundary.bnd BB)
    (LaxMonoidalAdjunction.bnd Holo))
  where

  module Frob = AdjMon.Frobenius Holo
  module Der  = AdjMon.Derived (LaxMonoidalAdjunction.core Holo) mono-ext mono-bnd

  private
    frobenius-ext≤-exists : _
    frobenius-ext≤-exists = Frob.frobenius-ext≤

    T-closureOp-exists : _
    T-closureOp-exists = Der.T-closureOp

module SheafQuotes {ℓ : Level} (CP : ConPreorder ℓ) where
  module FS = ForcingSheaves

  private
    coverage-exists : _
    coverage-exists = FS.Coverage

module NucleusMuQuotes {ℓ : Level} where
  private
    joinSemilattice-exists : _
    joinSemilattice-exists = NucleusMu.JoinSemilattice

    bottomCoherence-exists : _
    bottomCoherence-exists = NucleusMu.BottomCoherence
```

This note is a **view** (adapter) that connects LogOS’ core closure/refinement
machinery to standard topos-theoretic vocabulary *conservatively*:
it stays at the level of **nuclei/local operators** and the minimal
Beck–Chevalley/Frobenius-shaped coherence that is already implemented.

If you want the full topos package (finite limits, exponentials, subobject
classifier, tripos-to-topos, etc.), this file should be read as a *landing pad*
that identifies which parts are already present in LogOS and which parts would
be extra semantics/assumptions.

Interpretation (analogy):
this document is a derived presentation (“view”) over existing nucleus/sheaf and
adjunction coherence interfaces; it does not add logical power.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.

Scope (formal)
--------------
- Parameter: minimal boundary structure (`BulkBoundary`, `LaxMonoidalAdjunction`, and the reflection theorems cited below).
- This view is intentionally agnostic to any particular `Kernel Sig Q` instance.

Adapter mapping to the literature (quick table)
-----------------------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Nucleus / local operator (preorder-level) | `ClosureOp` / guarded closure `Flow` | Preorder-first; becomes posetal under antisymmetry. |
| Coverage/topology on a preorder (site, posetal shadow) | `ForcingSheaves.Coverage`, `ForcingSheaves.localClosure` | A coverage induces a local operator on predicates (analogy: Lawvere–Tierney topology in a posetal shadow). |
| Sheaves = pre-fixed points (hence fixed up to `≈`) | `ForcingSheaves.Sheaf`, `sheaf↔fixed` | Implemented at the preorder-of-predicates level. |
| Frobenius reciprocity (lax) | `AdjunctionMonads.Frobenius.frobenius-ext≤` | One-way inequality; matches LogOS’ lax/irreversible stance. |
| Beck–Chevalley (lax) | `LogOS/Theorems/CategoryTheory/BeckChevalley.agda` | Packaged as commutation squares up to refinement. |
| “Generated nucleus/closure” via μ | `LogOS/Theorems/Reflection/NucleusMu.agda` | Builds μ-generated closures; closure-operator packaging uses explicit ωCPO + a continuity witness for the step. |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital quantale in the finite-join sense (not complete); not used directly here, but becomes relevant when instantiating graded/budgeted kernels. |

Assumptions (explicit)
----------------------
- This file does **not** claim a full topos internalisation. The code supports nuclei/local-operator reasoning and some cheap hyperdoctrine-shaped coherence (Frobenius/BC) **at preorder strength**.
- Any upgrade to equality-level categorical structure requires explicit extensionality assumptions (antisymmetry/proof-irrelevance), as elsewhere in LogOS.
- μ/least-pre-fixed-point claims require explicit domain-theoretic hypotheses (ωCPO/finite-first style bundles); they are not global axioms.

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: nuclei/local operators, sheaves-as-(pre)fixed-points, and Frobenius/Beck–Chevalley-shaped coherence.
- Weaker/lax by default: everything is preorder/lax (posetal shadow), not a full topos internalisation; equality-level structure requires explicit extensionality assumptions.
- Added by ports/adapters: “presentation independence” is available as a port-level transport principle, rather than tied to a single internal syntax.
- Assumption-scoped: μ/limit claims require explicit ωCPO/continuity hypotheses; resource/budget structure enters only through graded/budgeted kernel instantiations.

Theorem spine (authoritative)
-----------------------------
- Frobenius + derived closure/interior: `LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda` (`Frobenius.frobenius-ext≤`, `Derived.T-closureOp`).
- Beck–Chevalley (lax squares + closure/interior transport): `LogOS/Theorems/CategoryTheory/BeckChevalley.agda`.
- Coverage/sheaves as (pre)fixed points of a local operator: `LogOS/Theorems/Reflection/ForcingSheaves.agda` (`Coverage`, `localClosure`, `sheaf↔fixed`).
- μ-generated nuclei/closures (explicit ωCPO + continuity hypotheses): `LogOS/Theorems/Reflection/NucleusMu.agda`.
- The prose below is explanatory; the statements above are the authoritative claims.

Realizability orientation (careful)
-----------------------------------
The most natural bridge from LogOS to realizability-flavoured topos thinking is:

- treat **code/proofs** (`Code`, refinement) as the “realizers” side (see the CHL
  view), and
- treat **stable truth** as the “sheafified/observable” fragment (closure pre-fixed
  points, hence fixed up to `≈`),

but this repository currently does *not* construct a full realizability tripos
or a tripos-to-topos pipeline. This document therefore only states the **shared
core** that is already mechanized (nuclei, sheaves-as-fixed-points, and
Beck–Chevalley/Frobenius-shaped coherence).

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- Categorical logic leg (2-categories, BC/Frobenius references): `docs/Views/CategoricalLogic.lagda.md`
- CHL capstone (code/proof/program reading): `docs/Views/CurryHowardLambek.lagda.md`
- Observer semantics (resource/budgeted stability): `docs/Views/ObserverSemantics.lagda.md`
