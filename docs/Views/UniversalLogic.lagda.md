<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Universal Logic (Abstract Logic, Institutions, Presentations)

```agda
{-# OPTIONS --safe #-}
module docs.Views.UniversalLogic where

-- Typechecked “view surface” for a universal-logic reading in the sense of the
-- mathematics literature (abstract logic / institutional semantics):
--
-- - separate “meaning” (satisfaction / closure) from “syntax” (presentations),
-- - treat translations as structure (not ad hoc encodings),
-- - and make interoperability operational by transporting certificates/tools.
--
-- LogOS’ contribution is to package the universal-logic spine in a way that is
-- preorder-first (lax) and mechanically honest about what is equality vs what
-- is only preserved up to satisfaction equivalence (↔).

open import LogOS.Prelude public

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.API.Views as Views
open Views.Kernels using (Kernel)

module ToolIO = Views.SatSystemIO
module BoundarySystemIO = Views.BoundarySystemIO
module InterlinguaCore = Views.PortsAdapters.Hetero
module Interop = Views.PortsAdapters.Interoperability
module CanonicalPorts = Views.PortsAdapters.CanonicalPorts
module Bootstrapping = Views.Bootstrapping

module Quotes where
  private
    presentationC-exists : _
    presentationC-exists = InterlinguaCore.PresentationC

    systemIO-exists : _
    systemIO-exists = ToolIO.SatSystemIO

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
  module CP = CanonicalPorts.For K

  private
    codePort-exists : _
    codePort-exists = CP.CodePort

    boundaryPort∂-exists : _
    boundaryPort∂-exists = CP.BoundaryPort∂

    bootstrap-iso-exists : _
    bootstrap-iso-exists = Bootstrapping.For.bootstrap-iso
```

Purpose
-------
This view presents LogOS as a piece of **universal logic infrastructure** in a
standard sense: it makes “logic” (meaning) and “presentation” (syntax/interface)
separable objects, and it treats translation as a first-class, checkable part of
the theory.

Concretely, LogOS factors the universal-logic picture into:

- a satisfaction relation (meaning),
- closure/refinement structure (consequence-like structure),
- presentations over the same satisfaction relation (ports),
- canonical translations between presentations (interlingua),
- and a way to transport external tools/certificates across presentations.

The emphasis is operational: the point is not only that presentations preserve
satisfaction (↔), but that **tool I/O** (proof search, model checking, certificates)
can be rebased across presentations automatically.

Relation to the universal-logic literature (orientation)
--------------------------------------------------------
The universal-logic literature packages logics in a small number of recurring
shapes. LogOS aligns with them as follows:

- **Abstract consequence/closure:** Tarskian consequence operators are closure
  operators; LogOS’ `Flow`/`ClosureOp` are closure operators on a preorder
  (preorder-first, so antisymmetry is an explicit strengthening).
- **Model theory / institutions:** a satisfaction relation is the core semantic
  object; LogOS treats the boundary satisfaction (`Sat_H_bnd`) as the canonical
  satisfaction relation for transport/presentation.
- **Structurality / signature change:** universal logic often builds logics over
  changing signatures (substitution/renaming). LogOS provides explicit signature
  morphisms (`SigHom`) and reindexing (`reindexKernel`) so
  “change of vocabulary” is an explicit, checkable transport.
- **Translations and equivalences:** universal logic studies maps between logics
  and when two presentations count as “the same logic” (adapter-equivalence). LogOS’ interlingua and
  adapter equivalence `Adapter≈` are the basic currency for this (always stated
  up to satisfaction equivalence (↔), not by syntactic identification).

Interpretation (analogy):
think “one satisfaction relation, many presentations”. The analogy is only meant to communicate
that presentations are derived interfaces over the same satisfaction relation;
the formal content is the imported/typechecked Agda surfaces below.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Notation (local)
----------------
- `c ⊑ d`: refinement/entailment in a preorder.
- `c ≈ d`: mutual refinement.
- `P ↔ Q`: satisfaction equivalence (paired implications).
- `Adapter≈`: adapter equivalence (pointwise satisfaction equivalence (↔) after mapping).
- `x ≡ y`: propositional equality (`_≡_`), not judgmental equality.

Scope (formal)
--------------
- Kernel-facing part: parameter `Kernel Sig Q` (to explain canonical ports and bootstrapping).
- Port/tooling part: stated for a generic satisfaction relation via `PresentationC` and `SatSystemIO`
  (no kernel-specific axioms needed).

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Logic (model-theoretic core) | `SatC : Ctx → Con → Set` | An “institutional” core: satisfaction without committing to one syntax. |
| Abstract consequence / entailment | preorder refinement `⊑`, closure operators (`ClosureOp`, `Flow`) | A closure operator on a preorder is the LogOS-native analogue of a Tarskian consequence operator (preorder-first). |
| Institution (fixed-signature shadow) | boundary satisfaction `Sat_H_bnd` | For a fixed signature, the boundary layer is a satisfaction relation of the right shape; see `KernelShape.Sat_H_bnd`. |
| Signature morphism / substitution discipline | `SigHom`, `reindexKernel` | Signature change is explicit and transport-first (no hidden substitution principle). |
| Presentation of a logic | `PresentationC`, `BoundaryPort` | A syntax/interface over a fixed satisfaction relation, with satisfaction equivalences (↔) as the correctness criterion. |
| Translation between presentations | `Interlingua.translate` | Canonical translation that preserves and reflects satisfaction (↔) for two presentations over the same `SatC`. |
| Equivalence of presentations | adapter equivalence `Adapter≈` | Two presentations/adapters are compared by pointwise satisfaction equivalence (↔) after translation. |
| Logic system with tools | `SatSystemIO` | Presentation + prover + model-checker; transports are structural. |
| Transport of tools across presentations | `SatSystemIO.rebase` | Pulls provers/model-checkers back along canonical translations. |
| Morphism between logics | `SatMor`, `SatSystemIO.rebaseAlongSatMor` | Satisfaction morphism + canonical pullback of tools; no surjectivity assumptions. |
| Canonical kernel presentations | `CanonicalPorts.For.CodePort`, `BoundaryPort∂` | Two ports over the same boundary satisfaction, derived from any kernel. |
| Canonical alignment (LogOS style) | `Bootstrapping.For.bootstrap-iso` | Bootstrapping is an `Adapter≈`-equivalence between the canonical code and boundary presentations. |

Core definitions (literature style)
-----------------------------------

**Definition (Logic, model-theoretic core).** In a universal-logic reading, one
can take the model-theoretic core of a logic to be a satisfaction relation
\[
  \mathrm{Sat}_C : \mathrm{Ctx} \to \mathrm{Con} \to \mathrm{Set}.
\]
LogOS’ ports/adapters spine is built around this shape (`PresentationC`, `SatMor`,
`SatSystemIO`) so that meaning can be held fixed while presentations vary.

**Definition (Logic, abstract consequence side).** Independently, an abstract
logic can be presented by an entailment preorder (refinement) together with a
closure operator. In LogOS this is expressed preorder-first:
`c ⊑ d` is entailment, and `Flow`/`ClosureOp` is a closure/nucleus on constraints.

This is the “consequence operator” side of universal logic: stable constraints
(pre-fixed points of the closure) play the role of “closed theories”.

**Definition (Presentation).** A presentation of a satisfaction relation chooses
a formula type `Form` and an interface between `Form` and the underlying `Con`,
together with satisfaction equivalences (↔) showing that the two ways of talking
about meaning agree. In LogOS this is `PresentationC` (kernel-independent) and
its boundary-specialized form `BoundaryPort`.

**Definition (Tool I/O).** A logic system with tooling is a `SatSystemIO`:
a name, a presentation, and proof-system interfaces for
global validity (“prover”) and context-indexed satisfaction (“model checker”).

**Definition (Rebasing).** If two presentations sit over the same satisfaction,
then tools can be pulled back along the canonical translation:
\[
  \mathrm{rebase} : \mathrm{SatSystemIO}(P_2) \to \mathrm{SatSystemIO}(P_1).
\]
Equivalently: `SatSystemIO` is contravariant in presentation translations (rebasing is pullback).
This is a structural transport theorem: it does not assume completeness or
soundness of the tools beyond what `ProofSystem` already encodes.

Assumptions (explicit)
----------------------
- No global “one true syntax”: the port spine keeps syntax/presentation separate from meaning.
- “Equivalence” is always qualified:
  satisfaction equivalence (↔), mutual refinement (≈), observational equality (`ObsEq…`), or adapter equivalence (`Adapter≈`).
- `rebaseAlongSatMor` is pullback-only: transporting *global* validity forward would require extra hypotheses (e.g. surjectivity of `mapCtx`), and LogOS does not assume this by default.

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: universal-logic separation of meaning (⊨) from syntax/presentation, and explicit translations between presentations.
- Weaker/lax by default: the core is preorder/lax; no implicit antisymmetry/proof-irrelevance; equality-level upgrades are explicit assumptions.
- Added by ports/adapters: forced interlingua translation and canonical adapter equivalence (`Adapter≈`) make “presentation independence” a theorem shape rather than a convention.
- Added by tooling: `SatSystemIO` packages provers/model-checkers and makes rebasing a one-liner (pullback of certificates), so interoperability is operational, not just semantic.

Theorem spine (authoritative)
-----------------------------
- Presentations and canonical translation:
  - `LogOS/Ports/Semantic/PresentationCore.agda` (`PresentationC`)
  - `LogOS/Ports/Semantic/Interlingua.agda` (`translate`, `translate-unique`, `translate-id`, `translate-comp`)
  - Thin-2-category bookkeeping for presentations (fixed satisfaction system):
    `LogOS/Ports/Semantic/Presentation2Cat.agda` and wrapper `LogOS/Theorems/CategoryTheory/Presentation2Ref2Cat.agda`.
- Adapters and adapter equivalence:
  - `LogOS/Ports/Semantic/Interoperability.agda` (`PortAdapter`, `Adapter≈`, `adapter-unique`, `adapter-confluent`)
- Tool I/O and rebasing:
  - `LogOS/Syntax/ProofSystem.agda` (`ProofSystem`)
  - `LogOS/Ports/Semantic/SatSystemIO.agda` (`SatSystemIO`, `rebase`, `rebaseAlongSatMor`)
  - `LogOS/Ports/Semantic/BoundarySystemIO.agda` (build/rebase `SatSystemIO` at the boundary port level)
  - `LogOS/Ports/Semantic/ProofTransport.agda` (pull back provers/model-checkers along translations)
- Kernel-derived canonical ports + bootstrapping:
  - `LogOS/Ports/Semantic/CanonicalPorts.agda` (`CodePort`, `BoundaryPort∂`, `code→Port`, `port→Code`)
  - `LogOS/Theorems/Meta/Bootstrapping.agda` (`bootstrap-iso`, uniqueness/confluence up to `Adapter≈`)
  - Signature transport: `LogOS/Kernel/Reindex.agda`.

Micro-example (rebasing a prover)
---------------------------------
Suppose two presentations \(P_1\) and \(P_2\) sit over the same satisfaction
\(\mathrm{Sat}_C\). If you have a prover/model-checker system for \(P_2\),
`SatSystemIO.rebase` gives you one for \(P_1\) by pulling back certificates along
the canonical translation.

In particular, for a kernel `K`, the two canonical boundary ports
(`CanonicalPorts.For.CodePort` and `BoundaryPort∂`) are `Adapter≈`-equivalent
(`Bootstrapping.For.bootstrap-iso`). So any tool you build against one of these
presentations can be rebased to the other without rewriting the tool interface.

Pointers (where to connect)
---------------------------
- If you want the “one kernel, many logics” story in model theory language, see `docs/Views/MultiInstitution.lagda.md`.
- If you want the 2-category packaging of adapter equivalence, see `docs/Views/CategoricalLogic.lagda.md`.
- If you want the CHL-facing capstone (proof/program/category bundle), see `docs/Views/CurryHowardLambek.lagda.md` and `docs/Views/MeredithSentences.lagda.md`.
- If you want the cross-view canonical contract for semantics terminology and transport rules, see `docs/Views/FormalSemantics.lagda.md`.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- Observer semantics (resource/telemetry interpretation): `docs/Views/ObserverSemantics.lagda.md`
- Topos framing (nuclei/sheaf orientation): `docs/Views/Topos.lagda.md`
