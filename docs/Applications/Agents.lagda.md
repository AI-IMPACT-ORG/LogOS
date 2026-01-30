<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Agents (Sockets, Monitoring, Auditing) (LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.Agents where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.Agents.Surface
import LogOS.Packs.Agents.Applications.All

```

This note is the publication-facing entrypoint for the **Agents** pack in the
LogOS library.

The pack stays intentionally lightweight: the kernel already contains most of the
agent-like structure (boundary endomaps, wiring, and fixed points). The Agents
docs therefore act as a navigation layer over kernel-level theorems.

Trust level:
- **stable** (lock surface: `LogOS/Packs/Agents/Surface.agda`)
- **experimental extensions** (see `docs/Applications/Agents_Experimental.lagda.md`;
  lock surface: `LogOS/Packs/Agents/Experimental/Surface.agda`)

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Wording discipline (guardrail)
------------------------------
This document uses domain terminology (“socket”, “agent”, “learning”, …) as
**interpretation**. The literal content is always the
referenced Agda interface/theorem. In particular:

- “Policy/update/training” = boundary constraints + monotone endomaps (and
  optional ωCPO/Kleene μ (limit) reasoning) inside the kernel algebra.
- Experimental analogy-heavy vocabulary (physics/RG/transformer scaling) is
  documented separately in `docs/Applications/Agents_Experimental.lagda.md` and
  is always marked as interpretation (not a literal theorem statement).

The core idea is to treat an “agent” as an **open system** with an explicit
boundary I/O view:

- **Ports:** designated interfaces like `Obs`, `Act`, `Reward`, `Oversight`, …
  (`LogOS/Packs/Agents/Socket/Ports.agda`).
- **Contracts:** functorial, signature-indexed boundary syntax `Con∂ Sig`
  (`LogOS/Packs/Agents/Socket/Contracts.agda`), interpreted by supplying a
  valuation `Iface → Con_bnd`.
- **Computation:** a scheme choice into a shared process (`SchemeCategory`),
  typically “kernel-as-process” via `KernelUniversalProcess`.
- **Safety:** monitoring/auditing is done at the *boundary constraint* level
  (`Con_bnd`), so it composes through ports/adapters and network wiring.

## The agent socket surface

The “socket” is the minimal interface needed to compare agent frameworks in a
kernel-native way:

- `LogOS/Packs/Agents/Socket/Core.agda` — `AgentSocket`
  (kernel + ports + contracts + process + choice).
- `LogOS/Packs/Agents/Socket/FromKernel.agda` — canonical constructors from any
  `Kernel` using `CodeProcess` / `BoundaryProcess`.
- `LogOS/Packs/Agents/Socket/FromGradedKernel.agda` — same for `GradedKernel`
  (budgeted/graded computation).

For resource-aware agent stories, prefer `FromGradedKernel`: the underlying
`KernelUniversalProcess.ForGradedKernel` assigns the one-step cost to the
kernel’s `step-grade`. The ungraded `FromKernel` constructors use the neutral
cost `e` (cost-free steps).

Recommended import:

```text
open import LogOS.Packs.Agents.Surface as Agents
```

Experimental extensions (physics/RG/transformer scaling) are documented in
`docs/Applications/Agents_Experimental.lagda.md`.

## Agent networks (heterogeneous wiring)

Agent networks are a lightweight layer over sockets: a **network** is just
role-indexed sockets plus explicit edge adapters. Heterogeneous agents are
first-class: each role can have its own signature/kernel, and edges are
**satisfaction morphisms** (`SatMor`) between boundary interfaces.

`SatMor` is conservative by construction: it preserves *and reflects*
satisfaction. This is stronger than mere soundness; if a use case only admits
one-way translation, it must be modeled with a different, explicitly weaker
adapter (not provided by the Agents pack).

This heterogeneity lets you keep mixed formalisms intact (e.g., symbolic and
statistical roles) while still composing them. When edges are `SatMor`, the
translation is explicit and satisfaction-preserving/reflecting at the boundary
semantics level, so overlaps and identifications are deliberate rather than
implicit.

- Core surface: `LogOS/Packs/Agents/Networks/Hetero.agda`
  - `AgentNode` and `AgentNetwork`: package per-role sockets.
  - `Edge`: a conservative translation between boundary satisfactions.
  - `edgeTensor` / `edgeUpdate`: wire an incoming constraint into a target
    policy by translating along the edge, then tensoring at the target.
- Port-level interoperability: `LogOS/Packs/Agents/Networks/Interop.agda`
  - Combine an `Edge` with boundary ports to obtain canonical formula
    translations via the heterogeneous interlingua.
- Monitor compatibility across edges: `LogOS/Packs/Agents/Networks/MonitorInterop.agda`
  - Ported-closure naturality specialized to network monitors (edge translations
    commute with monitor application up to satisfaction).
  - `defaultMonitor-compatible` shows the default monitor is compatible when
    the edge translation commutes with flow and tensoring-in safety.
- Network-as-agent wrapper: `LogOS/Packs/Agents/Networks/NetworkAgent.agda`
  - Pick a hub role, translate all role constraints to the hub, and aggregate.
- Aggregation is a parameter; any “network-as-agent” claim must name it.
- The aggregator is required to respect observational equality at the hub.
- Namespaced index surface: `LogOS/Packs/Agents/Networks/Core.agda` (and the lab surface).
- Minimal example: `LogOS/Packs/Agents/Examples/HelloNetwork.agda`.
- Concrete reindexing example: `LogOS/Packs/Agents/Examples/ReindexedNetwork.agda`.
  - Shows a non-identity signature map that collapses distinct atoms and
    exhibits the overlap both syntactically and semantically.

Minimal wiring snippet (via the concrete hetero example):

```agda
import LogOS.Packs.Agents.Examples.ReindexedNetwork as RN

translateExample : RN.Net.Con RN.left → RN.Net.Con RN.right
translateExample = RN.translateLeftToRight
```

If you need translation between **external syntaxes** (not just boundary
constraints), use the heterogeneous interlingua:
`LogOS/Ports/Semantic/HeteroInterlinguaCore.agda`. It combines a `SatMor` edge
with boundary ports to produce the canonical translation that preserves and
reflects satisfaction (↔).

## Monitoring and auditing (opacity-native)

The pack is intentionally “opacity-native”: it models auditors as
**decode-extensional (up to decoded mutual refinement in the kernel case, `_≈K_`) partial-output observers**, so the existing diagonal / opacity
meta-theorems apply as formal consequences of those observer definitions.

- Monitoring endomaps: `LogOS/Packs/Agents/Safety/Monitor.agda`
  - Canonical example: `defaultMonitor` — tensor in the safety contract, then
    saturate at the kernel’s `sat` grade (a design choice, not an unconditional
    guarantee).
- Auditor surface: `LogOS/Packs/Agents/Safety/Audit.agda`
  - `Auditor` is an `Oracle` wrapper for the spectral separation output interface,
    defined for any process (and hence for any socket).
- “No total budgeted auditor”: `LogOS/Packs/Agents/Safety/NoTotalAuditor.agda`
  - process-generic diagonalization barriers (non-totality, and “no total within budget”).
  - experimental proof-search instantiation: `LogOS/Packs/Agents/Experimental/Safety/NoTotalAuditor.agda`

## Kernel leverage (nuclei + fixed points)

The agent pack reuses kernel theorems directly; these are the main hooks for
monitoring/auditing and policy composition:

- `LogOS/Theorems/Reflection/QuanticNucleus.agda` — nucleus laws at the kernel boundary;
  nucleus-stable elements (pre-fixed points, hence fixed up to `≈`) form a quantale and the quotient map has the expected factorisation
  for `j`-invariant functions (`f (j x) ≡ f x`) for any
  quantale equipped with a nucleus (monotone/inflationary/idempotent‑lax, plus
  join/multiplication preservation up to `≈`). A canonical instance is the budget quantale
  `QAdapter.Scale` (via `quantaleFromQAdapter`). This does *not* require boundary
  constraints to be a quantale by default; when a model equips the boundary with
  compatible join/multiplication structure, the same theorem applies there too.
- `LogOS/Theorems/Boundary/LogicKernel/Mu.agda` — Kleene/μ support for closure steps,
  used for iterative monitors and convergence-to-safety arguments.
- `LogOS/Theorems/Meta/LimitPublicisation.agda` — stable/extensional predicates become
  observable (`Pr`), allowing audits to be justified from stability rather than
  explicit observation axioms.

## Learning surface (updates + fixed points)

Learning is expressed using the same kernel DSL as monitoring:

- A **policy** is a boundary constraint `Con_bnd`.
- An **update** is a monotone endomap on `Con_bnd`.
- A **learning step** is a closure step (id <= update <= Flow), so it composes
  and stays within the kernel's saturation envelope.

The concrete surfaces are lightweight wrappers:

- `LogOS/Packs/Agents/Learning/Core.agda` — policies, updates, and learning steps.
- `LogOS/Packs/Agents/Learning/FixedPoint.agda` — Kleene mu wrappers
  (`μPolicy`, unfolding, induction), so "training to convergence" is a
  kernel-native fixed-point statement.
- `LogOS/Packs/Agents/Learning/TrainingSoundness.agda` — minimal training
  soundness: learning steps preserve any lower bound (Safety/Objectives/Assumes
  are preserved when already satisfied).
- `μPolicy-step-fixed` (in `LogOS/Packs/Agents/Learning/FixedPoint.agda`) packages
  the “both directions” fixed‑point statement for a learning step under Scott
  continuity, giving a compact convergence‑to‑stability lemma.

High-level training loops can be modeled as updates on policies. The μ-policy
construction is available **once you supply an `OmegaCPO` on the boundary preorder**
(an explicit model-local assumption), and the stronger unfold-right direction
(hence “μ is fixed up to refinement”) additionally uses Scott/ω-continuity of the update endomap (also an
explicit assumption). This captures convergence inside the kernel rather than as
an external meta-argument.

## Interpretation (analogy): neural-symbolic LLM view (soft + hard constraints)

To make the neural-symbolic story explicit, the graded kernel machinery can be
used as a soft layer:

- **Soft updates:** `LogOS/Packs/Agents/Learning/SoftPolicy.agda` models a
  grade-indexed update (strength/temperature) using `ClosureStepAt` and the
  kernel's quantale scale.
- **Hard constraints:** symbolic rules are just `Con_bnd`; they blend with a
  soft policy using the boundary tensor (`_⊗∂_`).
- **Blend example:** `LogOS/Packs/Agents/Examples/NeuralSymbolicBlend.agda` shows
  the minimal pattern: apply a soft update, then refine by a symbolic constraint.

Interpretation (analogy): this provides a precise *soft/hard constraint* split in the
kernel algebra. Any claim about real LLM training only follows after you supply
an explicit training model and justify the chosen observables/budgets.

## Telemetry contracts (observation-only)

The telemetry story is spelled out as an **observation-only contract** on
boundary constraints:

- `LogOS/Packs/Agents/Telemetry.agda` — a `TelemetryContract` for any socket,
  with a monotone observation map and a “telemetry respects learning steps”
  lemma (no semantic effect on the kernel).
- `LogOS/Boundary/Telemetry.agda` — generic lemmas
  `telemetry-respects-≈∂` / `telemetry-respects-≈∂Cosp` show telemetry is stable
  under observational equality (so monitors can’t change satisfaction).

This lets the agent surface state telemetry obligations without smuggling in
operational effects: telemetry is just another boundary observer.

Experimental extensions (physics/RG/transformer scaling) are documented in
`docs/Applications/Agents_Experimental.lagda.md` (experimental lock surface:
`LogOS/Packs/Agents/Experimental/Surface.agda`).

## UniversalIR reuse (framework instances)

Frameworks are defined minimally as a `Choice` into a shared `Process`
(`LogOS/Packs/Agents/Frameworks/Core.agda`). The concrete embeddings currently
supplied are the UniversalIR paradigms (closed on the `PATask` input):

- `LogOS/Packs/Agents/Frameworks/UniversalIR.agda` (curated surface via
  `LogOS/Packs/UniversalIR/Core.agda`), which exports `UProcess` plus
  `minskyChoice`, `lambdaChoice`, `ethereumChoice`, `oracleChoice`,
  and `quantumCircuitChoice`.
- `LogOS/Packs/Agents/Frameworks/PATask.agda` packages these as
  `Framework` instances (`minskyFramework`, `lambdaFramework`, ...) so they can be
  plugged into an `AgentSocket` without extra boilerplate.
- Budgeted variants (explicit step bounds) are also provided by the same module,
  using `Bounded PATask` as the task type (`boundedMinskyFramework`, ...).

Agreement between the UniversalIR frameworks is available in two flavours:

- Machine-scheme agreement: `LogOS/Packs/Agents/Frameworks/PATaskAgreement.agda`
  re-exports the paper-facing `ParadigmsRunEq` statement.
- Choice-scheme agreement: the same module provides `ChoiceSchemesRunEq` for
  the UniversalIR `Choice`-based schemes (the ones used by `Framework`).

Other “known framework” modules are **mostly interfaces or meta-theory surfaces**;
when they include translations into UniversalIR, they are intentionally minimal:

- `LogOS/Packs/Agents/Frameworks/AIXI_Bounded.agda` and
  `LogOS/Packs/Agents/Frameworks/OOPS.agda` expose the generic `SchemeCategory`
  machinery, and now include minimal **bounded PATask** translations into
  `UProcess` (`aixiChoice`/`oopsChoice`, with `aixiFramework`/`oopsFramework`).
  These are checked instantiations, not full RL or optimal‑search models.
- `LogOS/Packs/Agents/Frameworks/GodelMachine.agda` and
  `LogOS/Packs/Agents/Frameworks/MetaReasoning.agda` re-export meta-theory
  (Lob/Godel/no-omniscience) rather than a concrete process translation.

So, at present: **UniversalIR is the main provided, checked integration** of
agent-like task languages into a shared process (`UProcess`), with reusable
transport/agreement tooling. To integrate another framework into UniversalIR, supply
a `Choice` into `UProcess` (and, if needed, a `ProcessHom`
or a cost/budget-carrying `ProcessHomCost` / `ProcessHomCostWithGrade`, or the
corresponding `mapChoice`/`mapChoiceLax` transport), then plug it into an
`AgentSocket`.

## Kernel-native frameworks (tasks = code or boundary constraints)

If you want the agent story to be “as LogOS-native as possible”, the kernel can
be treated as the shared process directly:

- `LogOS/Packs/Agents/Frameworks/KernelNative.agda` provides `codeFramework` and
  `boundaryFramework` constructors for `LogicKernel`, `Kernel`, and `GradedKernel`.
- The task type becomes either `Code` (execute a code fragment for a chosen fuel)
  or `Con_bnd` (evolve a boundary constraint for a chosen fuel).

This yields a kernel-internal agent substrate within the formal model: tasks are
literally the objects of the kernel’s own computational process.
