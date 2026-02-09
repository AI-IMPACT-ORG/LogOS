<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Futamura × Diagonal (Showcase)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.FutamuraDiagonal where

-- Sync guard: this file is a narrative, but it is typechecked. We keep the
-- imports shallow here and route through a curated “showcase surface”.
import LogOS.Packs.Showcase.FutamuraDiagonal as Show

private
  -- Futamura-1 (scheme-level) exists and is usable without any reflective code layer.
  futamura₁-run-exists : _
  futamura₁-run-exists = Show.futamura₁-run

  -- Concrete UniversalIR instance: fixed Minsky program/state/fuel witnesses.
  futamura₁-run-minsky-concrete : _
  futamura₁-run-minsky-concrete = Show.Spine.MinskyRun.futamura₁-concrete

  run≡observe-minsky-concrete : _
  run≡observe-minsky-concrete = Show.Spine.MinskyRun.run≡observe-concrete

  -- Classical (code-producing) Futamura projections are assumption-scoped.
  codeFutamura-exists : _
  codeFutamura-exists = Show.CodeFutamura

  -- Lawvere fixed point / diagonal packs (assumption-scoped).
  lawvereFix-exists : _
  lawvereFix-exists = Show.Diagonal.lawvereFix

  diagonalization-from-QuoteSubst-exists : _
  diagonalization-from-QuoteSubst-exists = Show.Diagonal.Diagonalization-from-QuoteSubst

  -- Presentation-independence currency: confluence of adapters between the same ports.
  adapter-confluent-exists : _
  adapter-confluent-exists = Show.Interoperability.For.adapter-confluent

  -- Operational payoff: rebasing tool I/O across presentations.
  rebase-exists : _
  rebase-exists = Show.SatSystemIO.rebase

  -- Bootstrapping iso (code port ↔ boundary port) exists (kernel-parameterised).
  bootstrap-iso-exists : _
  bootstrap-iso-exists = Show.Bootstrapping.For.bootstrap-iso

  -- Rebase endpoints for canonical code-port/boundary-port transport.
  rebase-to-code-exists : _
  rebase-to-code-exists = Show.Spine.Transport.rebase-to-code

  rebase-to-boundary-exists : _
  rebase-to-boundary-exists = Show.Spine.Transport.rebase-to-boundary

  -- Concrete proof-carrying tagged system and certificate transport.
  tagged-systemio-code-exists : _
  tagged-systemio-code-exists = Show.Spine.Transport.taggedSystemIO-code

  tagged-systemio-boundary-from-code-exists : _
  tagged-systemio-boundary-from-code-exists = Show.Spine.Transport.taggedSystemIO-boundary-from-code

  tagged-prover-complete-boundary-from-code-exists : _
  tagged-prover-complete-boundary-from-code-exists =
    Show.Spine.Transport.taggedProver-complete-boundary-from-code

  tagged-modelchecker-complete-boundary-from-code-exists : _
  tagged-modelchecker-complete-boundary-from-code-exists =
    Show.Spine.Transport.taggedModelChecker-complete-boundary-from-code

  boundary-valid-cert-from-code-exists : _
  boundary-valid-cert-from-code-exists = Show.Spine.Transport.boundary-valid-cert-from-code

  boundary-sat-cert-from-code-exists : _
  boundary-sat-cert-from-code-exists = Show.Spine.Transport.boundary-sat-cert-from-code
```

This note proposes a particularly illustrative demo of **presentation independence**
as a *workflow*:

1) stage an evaluator (Futamura-style),
2) build self-reference (diagonal/Lawvere-style),
3) transport the result across presentations (ports/adapters) without rewriting the proof/tooling layer.

The point is not to claim new metalogic; it’s to show how LogOS can make two
classical ideas feel like the *same move* under different interfaces.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

## The two artifacts (as the repo actually packages them)

### Futamura: staging as an interface operation

UniversalIR gives a total small-step evaluator (`stepU`/`simulate`) plus a
scheme/category interface for running code under an explicit step budget.

In `LogOS/UniversalIR/Futamura.agda`, Futamura-1 is packaged at the **scheme**
level:

- evaluator interface: `EvalI : Interface (UCode × ℕ) UProcess`
- residual runner: `RunS u : Scheme ℕ ℕ`
- correctness statement: `futamura₁-run` (specialising commutes with running)

This is already “presentation independence” in miniature: the same observable
result is obtained whether you run the evaluator on `(u , n)` or run the staged
residual on `n`, and the theorem is insensitive to which backend produced `u`.

The classical code-producing Futamura projections (2/3) are isolated as an
explicit assumption record:

- `CodeFutamura` in `LogOS/UniversalIR/Futamura.agda`

That record is intentionally minimal: it does not smuggle in quotation as a
kernel axiom; it forces you to say exactly what your “code as data + evaluator”
interface is.

### Diagonal: Lawvere fixed point as an explicit trust boundary

The diagonal/“self-reference” side is packaged in
`LogOS/Theorems/Meta/Assumptions/Diagonal.agda`.

Two layers are worth highlighting:

- **Decode-level fixed point** (Lawvere): `lawvereFix` produces a code `s` such
  that `decode s` and `decode (f s)` mutually refine, under an explicit
  internal-hom witness (`QuoteSubst⊑` / `InternalHomWitness`).
- **Provability-level diagonal lemma shape:** both
  `Diagonalization-from-InternalHom` and `Diagonalization-from-QuoteSubst`
  construct a `Diagonalization` record (`diag→` / `→diag`) from explicit
  representation packs and local decode-to-provability bridges.

This is very close in shape to the Futamura story: both are about
“representability + self-instantiation”, but one targets **execution/staging**
and the other targets **fixed points / self-reference**.

## Why these are “remarkably close” in LogOS

LogOS makes both patterns look like small, composable records:

- Futamura-2/3 wants a *staging operator* `mix` plus an evaluator `eval`.
- Lawvere/diagonal wants a *representation operator* plus a self-instantiation witness.

In classic literature, these two families are often discussed in different
communities (partial evaluation vs diagonal arguments). In this codebase, they
are deliberately made to rhyme:

- staging is treated as an interface combinator (`specializeInterface`);
- diagonalisation is treated as an internal-hom-style witness
  (`InternalHomWitness` / `QuoteSubst⊑`) plus a local “reflection into proof”
  bridge (`DecodeImp⊑` / `DecodeImp`).

This is also where the categorical connection becomes literal: the diagonal file
explicitly presents the construction as a Lawvere-style fixed point.
See `docs/Paper/references.bib` (Lawvere, 1969).

## How this showcases the *general* LogOS approach

The deep-dive walkthrough structures this as a three-leg
pipeline that never commits to a privileged syntax:

1) **Pick a satisfaction boundary** (what counts as “observable truth”).
2) **Expose multiple presentations** (ports): code port, boundary port, IR ports, etc.
3) **Prove/assume self-reference once**, then transport it across presentations.

The architectural hooks are already there:

- canonical translation + uniqueness/confluence: `LogOS/Ports/Semantic/Interlingua.agda`,
  `LogOS/Ports/Semantic/Interoperability.agda`
- bootstrapping equivalence (code port ↔ boundary port): `LogOS/Theorems/Meta/Bootstrapping.agda`
- tool transport (“rebasing”): `LogOS/Ports/Semantic/SatSystemIO.agda`

The demo output is:

- a staged evaluator (Futamura-1) for a concrete UniversalIR backend,
- a diagonal witness (Lawvere/diagonal lemma pack) phrased at the code port,
- and the same witness rebased to the boundary port so that external tools
  consume it without any syntax-aware glue.

Concrete anchor now shipped:

- `LogOS/Packs/Showcase/FutamuraDiagonalSpine.agda` (`MinskyRun`) provides a
  fixed Minsky program/state/fuel witness for `futamura₁-run` and
  `run≡observe-simulate`.
- The same module (`Transport`) exports kernel-parameterised
  `rebase-to-code` / `rebase-to-boundary` entrypoints for canonical
  code-port/boundary-port rebasing.
- `Transport` also ships a proof-carrying tool surface (`taggedSystemIO-code`)
  and rebased variants (`taggedSystemIO-boundary-from-code`,
  `taggedSystemIO-code-from-boundary`) with exported completeness transfers and
  certificate constructors (`boundary-valid-cert-from-code`,
  `boundary-sat-cert-from-code`). The checker is nontrivial: it validates a
  syntax tag (`claimedTag ≡ inputTag`) on a tagged code fragment, instantiated
  via the generic `keyValidated` checker combinator in
  `LogOS/Syntax/ProofSystem.agda`.

## Current status and optional hardening

The full walkthrough module is now in
`docs/DeepDive/FutamuraDiagonal_Showcase.lagda.md`; this application note is the
short entrypoint, and the deep-dive is the buildable narrative.

Optional hardening step (not required for the current story):

1) Upgrade the current tag-consistency checker to a replay checker for one
   concrete instruction fragment (for example a bounded Minsky trace), while
   preserving the same rebase/completeness transport proofs over
   `CodePort`/`BoundaryPort∂`.
