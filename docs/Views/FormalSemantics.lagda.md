<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Formal Semantics (Canonical Contract)

```agda
{-# OPTIONS --safe #-}
module docs.Views.FormalSemantics where

-- Typechecked “view surface” for the canonical semantics contract.
--
-- Goal: collect the semantic invariants that are shared across the model-theory,
-- universal-logic, observer, and controlled-feedback readings.
--
-- Policy: this view is contract-first. It does not add logical power and does
-- not define a new kernel; it only names and bundles existing theorem surfaces.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.API.Views as Views
open Views.Kernels using (Kernel)

module ToolIO = Views.SatSystemIO
module BoundarySystemIO = Views.BoundarySystemIO
module Interop = Views.PortsAdapters.Interoperability
module Hetero = Views.PortsAdapters.Hetero
module CanonicalPorts = Views.PortsAdapters.CanonicalPorts
module ViewSatMor = Views.ViewSatMor
module Bootstrapping = Views.Bootstrapping

module Quotes where
  private
    presentationC-exists : _
    presentationC-exists = Hetero.PresentationC

    rebase-exists : _
    rebase-exists = ToolIO.rebase

    rebaseAlongSatMor-exists : _
    rebaseAlongSatMor-exists = ToolIO.rebaseAlongSatMor

    systemIOFromBoundaryPort-exists : _
    systemIOFromBoundaryPort-exists = BoundarySystemIO.systemIOFromBoundaryPort

    adapter≈-exists : _
    adapter≈-exists = Interop.For.Adapter≈

    adapter-confluent-exists : _
    adapter-confluent-exists = Interop.For.adapter-confluent

module KernelQuotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = Views.ViewTheorems.For K
  module CP = CanonicalPorts.For K

  private
    coh-SH-exists : _
    coh-SH-exists = V.MultiInstitution.coh-SH

    coh-H∂-exists : _
    coh-H∂-exists = V.MultiInstitution.coh-H∂

    entails∂-exists : _
    entails∂-exists = V.ObserverSemantics.Entails∂

    entails∂-budget-exists : _
    entails∂-budget-exists = V.ObserverSemantics.Entails∂-budget

    sound-complete∂-budget-exists : _
    sound-complete∂-budget-exists = V.ObserverSemantics.sound-complete∂-budget

    projection-exists : _
    projection-exists = V.Projections.projection

    codePort-exists : _
    codePort-exists = CP.CodePort

    boundaryPort∂-exists : _
    boundaryPort∂-exists = CP.BoundaryPort∂

    satMor-strict-to-boundary-exists : _
    satMor-strict-to-boundary-exists = ViewSatMor.satMor-strict-to-boundary

    satMor-code-to-boundary-exists : _
    satMor-code-to-boundary-exists = ViewSatMor.satMor-code-to-boundary

    bootstrap-iso-exists : _
    bootstrap-iso-exists = Bootstrapping.For.bootstrap-iso
```

Purpose
-------
This is the canonical **formal semantics contract** for the views folder.

It answers: what is semantically invariant in LogOS, independent of whether you
read the system through model theory, universal logic, observer semantics, or
controlled feedback.

Interpretation (analogy):
if other views are domain dictionaries, this file is the shared semantic ABI.
The analogy is orientation only; the formal content is the typechecked Agda
surface above.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Notation (local)
----------------
- `c ⊑ d`: refinement/entailment in a preorder.
- `c ≈ d`: mutual refinement.
- `P ↔ Q`: satisfaction equivalence.
- `x ≡ y`: propositional equality (`_≡_`), not judgmental equality.

Scope (formal)
--------------
- Parameterized kernel surface: `Kernel Sig Q`.
- Kernel-independent presentation/translation surface: `PresentationC`,
  interlingua/adapters, and `SatSystemIO` rebasing.
- No new axioms and no new computational model.

Assumptions (explicit)
----------------------
- No hidden strengthening: this view only re-bundles existing theorem surfaces.
- Equivalence is always relation-qualified (`↔`, `≈`, `Adapter≈`, `≡`), never
  silently collapsed.
- Completeness/adequacy claims remain conditional on explicit hypotheses.

Semantic contract (normative)
-----------------------------
1. **Meaning is explicit:** semantics is carried by named satisfaction relations
   (`Sat_S`, `Sat_H`, `Sat_H_bnd`) and explicit coherence maps between them.
2. **Transport is explicit:** signature change and presentation change are
   first-class morphisms (`SigHom`, `SatMor`, interlingua/adapters), not meta-level convention.
3. **Representation independence is partial, not total:** claims must factor
   through an explicit boundary residual (the semantic cut), not through raw representations.
4. **Tooling follows semantics:** provers/model-checkers transport by rebasing
   along semantic morphisms (`rebase`, `rebaseAlongSatMor`), preserving meaning-level obligations.
5. **Completeness is assumption-scoped:** any completeness/adequacy statement
   is conditional and must expose hypotheses (including budgeted and non-vacuity forms).

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: semantics-first presentation via satisfaction relations and
  morphism-based transport.
- Added by LogOS: a single, explicit residual-boundary rule that unifies
  representation-independence claims across all views.
- Added by tooling: rebasing is a typed interface (`SatSystemIO`) rather than an
  external convention.
- Assumption-scoped: completeness and stronger identifications remain explicit
  hypotheses, not global defaults.

Dictionary (literature ↔ LogOS)
-------------------------------

| Semantics notion | LogOS identifier(s) | Contract meaning |
|---|---|---|
| Satisfaction relation | `Sat_S`, `Sat_H`, `Sat_H_bnd` | Meaning is an explicit relation, not hidden in syntax. |
| Cross-tier coherence | `coh-SH`, `coh-H∂` | Tier translations are theorem-level (`↔`) obligations. |
| Presentation semantics | `PresentationC` | Syntax/presentation is separated from fixed meaning. |
| Canonical translation | interlingua + canonical adapter | Translation is structural, not ad hoc rewriting. |
| Semantic morphism | `SatMor` + view-induced `satMor-*` | Cross-system transport is explicit and typed. |
| Representation equivalence | `Adapter≈` | Equality claim at boundary is stated as observational equality (`↔`), not syntactic identity. |
| Tool transport | `SatSystemIO.rebase`, `SatSystemIO.rebaseAlongSatMor` | Certified pullback of prover/model-checker interfaces. |
| Canonical kernel alignment | `bootstrap-iso` | Code-port and boundary-port are equivalent as semantics presentations. |

Core definitions (literature style)
-----------------------------------

**Definition (Semantic object).** A semantic object is a satisfaction relation
\(Sat : Ctx \to Con \to Set\) together with explicit morphisms that transport
contexts/constraints while preserving and reflecting satisfaction.

**Definition (Residual boundary).** A residual boundary is the chosen semantic
cut used for representation independence: two representations are identified
only insofar as they induce equivalent boundary satisfaction behaviour.

**Definition (Partial representation independence).** A statement is
representation independent when it is invariant under the chosen residual
boundary transport (typically `Adapter≈`/`SatMor`), while still retaining the
residual distinctions that are intentionally observable at that boundary.

Residual-boundary rule (how to write sharp claims)
--------------------------------------------------
For any theorem intended to be representation independent, use this pattern:

1. choose a residual boundary map and name it,
2. phrase predicates on boundary meaning (not raw code/syntax),
3. prove transport along the semantic morphism (`SatMor`/adapter),
4. state exactly what residual distinctions remain observable.

This is the shortest route to your “partial representation independence” goal:
the residual boundary is the only quotient you need, and it keeps claims strong
without collapsing intended semantic structure.

Theorem spine (authoritative)
-----------------------------
- Tier coherence and observer entailment:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `MultiInstitution`, `ObserverSemantics`, `Projections`).
- Presentation + interoperability:
  `LogOS/Ports/Semantic/HeteroInterlinguaCore.agda`,
  `LogOS/Ports/Semantic/Interoperability.agda`.
- View-induced semantic morphisms:
  `LogOS/Adapters/Views/SatMor.agda` (`satMor-strict-to-boundary`, `satMor-code-to-boundary`).
- Tool rebasing:
  `LogOS/Ports/Semantic/SatSystemIO.agda`,
  `LogOS/Ports/Semantic/BoundarySystemIO.agda`.
- Canonical code/boundary equivalence:
  `LogOS/Ports/Semantic/CanonicalPorts.agda`,
  `LogOS/Theorems/Meta/Bootstrapping.agda` (`bootstrap-iso`).

Non-goals (keeps this view manageable)
--------------------------------------
- No physics interpretation details (see `docs/Views/ObserverSemantics.lagda.md`).
- No transformer architecture modelling details (see `docs/Views/ControlledFeedback.lagda.md`).
- No additional proof power or new axioms.

Micro-example (observational equality under presentation change)
----------------------------------------------------
Given a kernel `K`, there are canonical boundary presentations `CodePort` and
`BoundaryPort∂`. `bootstrap-iso` states they are equivalent up to adapter
equivalence (`Adapter≈`). Therefore:

- semantics-level claims at the boundary can be moved between these
  presentations without changing truth conditions, and
- tooling attached to one presentation can be rebased to the other using the
  `SatSystemIO` transport layer.

Pointers (complementary views)
------------------------------
- Model-theoretic framing: `docs/Views/MultiInstitution.lagda.md`.
- Presentation/tooling framing: `docs/Views/UniversalLogic.lagda.md`.
- Observer/resource framing: `docs/Views/ObserverSemantics.lagda.md`.
- Controlled-feedback framing: `docs/Views/ControlledFeedback.lagda.md`.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- Categorical logic framing: `docs/Views/CategoricalLogic.lagda.md`
- CHL capstone framing: `docs/Views/CurryHowardLambek.lagda.md`
- Meredith compact anchors: `docs/Views/MeredithSentences.lagda.md`
