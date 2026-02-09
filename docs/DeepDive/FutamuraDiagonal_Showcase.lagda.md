<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Deep Dive — Futamura × Diagonal (Showcase Walkthrough)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.FutamuraDiagonal_Showcase where

open import LogOS.Prelude

-- We deliberately import the “real” modules here (deep-dive docs are allowed to
-- do that). The application note routes through a pack surface.
import LogOS.UniversalIR.Futamura as Futamura
import LogOS.Theorems.Meta.Assumptions.Diagonal as Diag
import LogOS.Theorems.Meta.Bootstrapping as Bootstrapping
import LogOS.Packs.Showcase.FutamuraDiagonalSpine as Spine

import LogOS.Ports.Semantic.Interlingua as Interlingua
import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Ports.Semantic.SatSystemIO as SatSystemIO

private
  -- Futamura-1 (scheme-level, UniversalIR semantic center).
  futamura₁-run-exists : _
  futamura₁-run-exists = Futamura.futamura₁-run

  -- Classical Futamura-2/3 (code-producing) are assumption-scoped.
  codeFutamura-exists : _
  codeFutamura-exists = Futamura.CodeFutamura

  -- Concrete UniversalIR instance from the shared showcase spine.
  futamura₁-run-minsky-concrete : _
  futamura₁-run-minsky-concrete = Spine.MinskyRun.futamura₁-concrete

  run≡observe-minsky-concrete : _
  run≡observe-minsky-concrete = Spine.MinskyRun.run≡observe-concrete

  -- Lawvere fixed point (decode-level) and diagonal lemma pack (provability-level).
  lawvereFix-exists : _
  lawvereFix-exists = Diag.lawvereFix

  diagonalization-from-InternalHom-exists : _
  diagonalization-from-InternalHom-exists = Diag.Diagonalization-from-InternalHom

  diagonalization-from-QuoteSubst-exists : _
  diagonalization-from-QuoteSubst-exists = Diag.Diagonalization-from-QuoteSubst

  -- Canonical translation + confluence.
  translate-unique-exists : _
  translate-unique-exists = Interlingua.translate-unique

  adapter-confluent-exists : _
  adapter-confluent-exists = Interop.For.adapter-confluent

  -- Tool transport.
  rebase-exists : _
  rebase-exists = SatSystemIO.rebase

  rebase-to-code-exists : _
  rebase-to-code-exists = Spine.Transport.rebase-to-code

  rebase-to-boundary-exists : _
  rebase-to-boundary-exists = Spine.Transport.rebase-to-boundary

  tagged-systemio-code-exists : _
  tagged-systemio-code-exists = Spine.Transport.taggedSystemIO-code

  tagged-systemio-boundary-from-code-exists : _
  tagged-systemio-boundary-from-code-exists = Spine.Transport.taggedSystemIO-boundary-from-code

  tagged-prover-complete-boundary-from-code-exists : _
  tagged-prover-complete-boundary-from-code-exists =
    Spine.Transport.taggedProver-complete-boundary-from-code

  tagged-modelchecker-complete-boundary-from-code-exists : _
  tagged-modelchecker-complete-boundary-from-code-exists =
    Spine.Transport.taggedModelChecker-complete-boundary-from-code

  boundary-valid-cert-from-code-exists : _
  boundary-valid-cert-from-code-exists = Spine.Transport.boundary-valid-cert-from-code

  boundary-sat-cert-from-code-exists : _
  boundary-sat-cert-from-code-exists = Spine.Transport.boundary-sat-cert-from-code

  -- Bootstrapping iso exists (kernel-parameterised).
  bootstrap-iso-exists : _
  bootstrap-iso-exists = Bootstrapping.For.bootstrap-iso
```

This note is the full walkthrough companion to
`docs/Applications/FutamuraDiagonal.lagda.md`. It is written as a buildable
demo outline: every pointer is backed by a typechecked surface.

The high-level goal is to demonstrate what LogOS is good at:

- make “representation/presentation choices” explicit (ports/presentations),
- make translations canonical and unique up to satisfaction equivalence (`↔`),
- and make theorems/tools transport along those translations.

## Part A — Futamura, but phrased as a LogOS-native transport theorem

Futamura is usually explained in terms of an interpreter and a partial evaluator.
In LogOS, the first projection is available *without* assuming a reflective
code layer:

- the evaluator is an `Interface` into a shared `Process`,
- staging is `specializeInterface`,
- and the “projection” is just a theorem about `run`.

See `LogOS/UniversalIR/Futamura.agda`:

- `EvalI : Interface (UCode × ℕ) UProcess`
- `RunS : UCode → Scheme ℕ ℕ`
- `futamura₁-run : ∀ u n → run (RunS u) n ≡ run EvalS (u , n)`

For a concrete anchor, see `LogOS/Packs/Showcase/FutamuraDiagonalSpine.agda`
(`MinskyRun.futamura₁-concrete`, `MinskyRun.run≡observe-concrete`).

The important part for the architecture story is that this is **presentation
aware**:
the evaluator takes input `(program , fuel)`, while the residual runner takes
input `fuel`. Both are presentations of the same underlying computation.

If you want an explicit “representation invariance” lemma in this style (but
for arbitrary processes and grade-indexed execution), the engine is:
`LogOS/Computation/SchemeCategory.agda` (`run≤-map`, `run≤-meaning-comm`).

## Part B — Diagonal, but isolated as a small assumption pack

The diagonal lemma / self-reference is intentionally kept out of the kernel
core. In LogOS it appears as explicit assumption records with the smallest
interfaces needed to run the argument.

See `LogOS/Theorems/Meta/Assumptions/Diagonal.agda`:

- **Lawvere fixed point (decode-level):**
  either `InternalHomWitness` or `QuoteSubst⊑` gives `lawvereFix`, producing
  `s` such that `decode s` and `decode (f s)` mutually refine.
- **Provability-level diagonalization (diagonal lemma shape):**
  both `Diagonalization-from-InternalHom` and
  `Diagonalization-from-QuoteSubst` construct the same `Diagonalization`
  surface from explicit decode-to-provability bridges.

The point is architectural: a “diagonal move” is a *thing you import* across a
trust boundary, not something that silently leaks in via a global axiom.

## Part C — The bridge: presentation independence (ports/adapters)

To make Futamura and diagonal feel like “one move”, we need a stable currency
for changing presentations.

In LogOS, that currency is:

- `PresentationC` (a presentation of a satisfaction relation),
- canonical translation `translate` (route via meaning),
- uniqueness/confluence up to satisfaction equivalence (`↔`),
- and tool transport (`SatSystemIO.rebase`).

See:

- `LogOS/Ports/Semantic/PresentationCore.agda` (`PresentationC`, `PresentationHom`)
- `LogOS/Ports/Semantic/Interlingua.agda` (`translate`, `translate-unique`)
- `LogOS/Ports/Semantic/Interoperability.agda` (`adapter-confluent`, `Adapter≈`)
- `LogOS/Ports/Semantic/SatSystemIO.agda` (`rebase`)
- `LogOS/Theorems/Meta/SemanticsTransport.agda` (`translate-id`, `translate-comp-presentations`, `translate-comp`)
- `LogOS/Packs/Showcase/FutamuraDiagonalSpine.agda` (`Transport.rebase-to-code`, `Transport.rebase-to-boundary`)

For concrete certificate transport (not only theorem transport), the same spine
module exports:

- `Transport.taggedSystemIO-code`, `Transport.taggedSystemIO-boundary-from-code`,
  `Transport.taggedSystemIO-code-from-boundary`
- completeness transfer witnesses
  (`Transport.taggedProver-complete-boundary-from-code`,
  `Transport.taggedModelChecker-complete-boundary-from-code`)
- certificate constructors
  (`Transport.boundary-valid-cert-from-code`,
  `Transport.boundary-sat-cert-from-code`)
- a nontrivial checker criterion on the fragment (`claimedTag ≡ inputTag`),
  which is decidable and preserved under rebasing; this is built from the
  generic `keyValidated` checker in `LogOS/Syntax/ProofSystem.agda`.

The “wow” part of the demo is that the *syntax-facing* differences disappear:
you state your theorem once in the presentation where it’s easiest, and then
you rebase it to the presentation where it’s operationally useful.

## Part D — Bootstrapping makes “code vs boundary” just another presentation choice

Bootstrapping makes the reflective code port and the canonical boundary port
`Adapter≈`-equivalent as ports.

See `LogOS/Theorems/Meta/Bootstrapping.agda` (`bootstrap-iso`).

This is the missing link for the “Futamura × diagonal” pitch:

- Futamura wants to talk about evaluators/partial evaluators over code-ish objects.
- The diagonal lemma wants to talk about “self reference” in a code-ish language.
- Bootstrapping lets you transport statements between code syntax and boundary
  constraint syntax *as presentations of the same satisfaction*.

## Part E — Budgeted self-reference: controlled feedback

The “self-reference” story is budgeted by construction: feedback lives in an
explicit **compute‑then‑stabilise** interface (`Flow`, `Box`, `Th*`) rather than
as a silent global μ/least pre-fixed point.

Concretely, this shows up as a small chain of checked surfaces:

- operational one‑step evolution `FlowCode = Guard ∘ Body` commuting with `decode`:
  `docs/DeepDive/Communication.lagda.md`
- view note (dictionary + transistor/feedback interpretation boundary):
  `docs/Views/ControlledFeedback.lagda.md`
- maximal fragment that is stable under this communication discipline (`Comm⋆`)
  and its induced projector/interior operator (`Pr`):
  `LogOS/Theorems/Meta/CommunicableTruth.agda`
- graded/budgeted variant (how finite/bounded observation supports stability claims):
  `LogOS/Theorems/Meta/BudgetedCommunicableTruth.agda`

This is “fractal” in the sense that the same move repeats at multiple layers:
pick a presentation/port, get a canonical translation, then transport theorems
and tools along it — while fixed points and diagonal moves stay explicit and
resource-aware.

## Optional hardening (not required for the current showcase)

1) Upgrade the current tag-consistency checker to a replay checker for one
   concrete instruction fragment (for example a bounded Minsky trace), while
   preserving the same rebase/completeness transport statements over
   `CodePort`/`BoundaryPort∂`.

The intention is that this becomes a template for future “showcases”: keep the
assumptions explicit, package the transports, and then reuse them everywhere.
