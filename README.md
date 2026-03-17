<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS

LogOS is a host-minimal Agda library for modular logics whose "guarded boundaries" are modular logics, yielding intrinsically recursive architecture. It treats interfaces as preorders of observable constraints, packages implementations as kernels, and makes additional structure explicit through ports, displayed layers, and upgrade ledgers. 

Novel here is the possibility for two different logic systems to have an own logic, and to share a third common communication logic. This is a prerequisite for true modularity. Technically this is done by downgrading to weak (i.e. general) mathematical building blocks. 

LogOS vision is to have an operating system for modular logic systems as a logic system. The more immediate goal is to have an agda library for a clean formal methods version of very general systems engineering for distributed processes. This is done through constructing the model of an intensional, functorial, logic programming language inside Agda with, optionally, explicit side-effects.

The repository is written for auditability:

- the core compiles under `--safe`, `--no-libraries`, `--without-K`, `--W all --W error` compiler flags 
- assumptions and axioms are surfaced as parameters or records rather than ambient axioms;
- public explanations that double as agent instructions are kept in literate Agda documents and policy scripts.
- CI targeting architectural clarity as well as known anti-patterns

This repository was developed with coding agents of various types over a long period of experimentation. There are true design choices inside the code as a choice of architecture. There are certainly other choices of presentation possible.

## Coding-agent on-ramp

The learning curve of this repository is practically vertical for most humans requiring abstract logic, category theory and advanced programming language theory concepts. Note though that from all those subjects only a small sliver is needed to understand the codebase. This is not an instrinsic blocker, as a personalised learning-by-doing is available using coding agents to translate between the structures in the repository and a domain language the operator understands and can check. As the repository involves foundational logic, such a map can *always* be found.

This entire repository is designed for human-AI collaboration. The shortest reliable on-ramp is:

1. Download the repository.
2. Install Agda and verify the full repository gate using `make check-all`.
3. Ask a coding agent to familiarise itself with the repository as a priming step.
4. Start by asking for an orientation: what the LT core is, what the ports are,
   how the application packs instantiate the patterns, and which invariants are
   non-negotiable.

If you only want to learn, you can skip step 2 in principle, but this is not recommended.

The minimal priming set for a coding agent is:

- repo instructions: [`AGENTS.md`](AGENTS.md)
- core route: [`docs/Core/README.md#start-here`](docs/Core/README.md#start-here)
- core overview: [`docs/Core/Orientation/LogOS_Overview.lagda.md`](docs/Core/Orientation/LogOS_Overview.lagda.md)
- contributor route: [`docs/Interpretations/Paths/Contributing.lagda.md`](docs/Interpretations/Paths/Contributing.lagda.md)
- guardrails: [`docs/Core/Policy/Guardrails_AI_Assisted_Development.md`](docs/Core/Policy/Guardrails_AI_Assisted_Development.md)
- architecture: [`docs/Core/Architecture/Diagram.lagda.md`](docs/Core/Architecture/Diagram.lagda.md)
- curated LT API: [`LogOS/API/LT.agda`](LogOS/API/LT.agda)

Working model for AI-assisted changes:

- assistants propose definitions, axiom packs, and translation layers
- Agda checks the resulting obligations
- CI policies check architectural constraints so semantic boundaries do not
  silently collapse
- coding agents should not change the main `README.md` without asking first
- humans check coding agents, at the very least through out-of-conversation review.

Start with `make toolchain-check` if the environment is new. For local iteration,
use `make check-core-warm`; for a full warm run without `clean`, use `make check-all-warm`;
before AI/LLM hand-off, run `make check-all`.

## Quick start

Build gates:

- Policy lane: `make check-policy`
- Core Agda lane: `make check-core`
- Integration Agda lane: `make check-integration`
- Docs lane: `make check-docs`
- Library smoke lane: `make check-lib`
- Warm core lane (no clean): `make check-core-warm`
- Warm full lane (no clean): `make check-all-warm`
- Everything (clean + all lanes): `make check-all`
- AI/LLM hand-off gate: `make check-all`
- Selected HTML entrypoints: `make html`

Telemetry runs write timestamped module timing TSVs under `_build/telemetry/`.

## Scope and status

What this repository currently provides:

- a typed LT core under `LogOS/LT/**`;
- a ports layer under `LogOS/Ports/**` for optional doctrines, contracts, quotation, causality, and related interfaces;
- downstream application packs under `LogOS/Apps/**`, including a ZFC development;
- executable policy checks that keep the architectural story aligned with the code.

What this repository does not currently claim:

- that every application-facing interpretation is complete or canonical;
- that the downstream packs settle domain questions outside the formal surfaces they explicitly define;
- that every construction here matches any single textbook formulation without qualification. Note that generally the concepts in the repository are more general than textbook ones. 

Independent semantic validation beyond the mechanised development remains future work. External semantic verification is outstanding. 
Several downstream packs are intentionally presented as scaffolds or examples rather than as finished domain developments.

## Documentation entrypoints

Start with the docs hub, then pick a path:

- Docs hub: [`docs/README.md`](docs/README.md)
- Core (specs, architecture, policy): [`docs/Core/README.md#start-here`](docs/Core/README.md#start-here)
- Results (theorem surfaces): [`docs/Results/README.md`](docs/Results/README.md)
- Patterns (reusable construction rules): [`docs/Patterns/README.md`](docs/Patterns/README.md)
- Interpretations (paths, views, applications): [`docs/Interpretations/README.md#start-here`](docs/Interpretations/README.md#start-here)
- Generated inventories: [`docs/Generated/README.md`](docs/Generated/README.md)
- Guardrails overview: [`docs/Core/Policy/Guardrails_AI_Assisted_Development.md`](docs/Core/Policy/Guardrails_AI_Assisted_Development.md)
- Repository lane contract: [`docs/Core/Project/Repository_Contract.md`](docs/Core/Project/Repository_Contract.md)

Contributor invariants, including AI-assistant rules, live in [`AGENTS.md`](AGENTS.md).

Useful entrypoints:

- Mathematics: [`docs/Interpretations/Paths/Mathematics.lagda.md`](docs/Interpretations/Paths/Mathematics.lagda.md)
- Physics: [`docs/Interpretations/Paths/Physics.lagda.md`](docs/Interpretations/Paths/Physics.lagda.md)
- Systems/physics view: [`docs/Interpretations/Views/Systems_And_Physics.lagda.md`](docs/Interpretations/Views/Systems_And_Physics.lagda.md)
- Irreversible transformers: [`docs/Patterns/Irreversible_Transformers.lagda.md`](docs/Patterns/Irreversible_Transformers.lagda.md)
- Programming language theory: [`docs/Interpretations/Paths/PLT.lagda.md`](docs/Interpretations/Paths/PLT.lagda.md)
- Systems / architecture: [`docs/Interpretations/Paths/Systems.lagda.md`](docs/Interpretations/Paths/Systems.lagda.md)
- Curated optional physics API: [`LogOS/API/Ports/PhysicalOptional.agda`](LogOS/API/Ports/PhysicalOptional.agda)
- Curated optional physics subroutes: [`Causal`](LogOS/API/Ports/PhysicalOptional/Causal.agda), [`Landauer`](LogOS/API/Ports/PhysicalOptional/Landauer.agda), [`Deutsch`](LogOS/API/Ports/PhysicalOptional/Deutsch.agda), [`PreQuantum`](LogOS/API/Ports/PhysicalOptional/PreQuantum.agda)
- Contributors: [`docs/Interpretations/Paths/Contributing.lagda.md`](docs/Interpretations/Paths/Contributing.lagda.md)
- Summit capstone: [`docs/Results/Summit.lagda.md`](docs/Results/Summit.lagda.md)

## Architecture in code

- LT core: [`LogOS/API/LT.agda`](LogOS/API/LT.agda) with implementations under [`LogOS/LT/`](LogOS/LT/)
- Ports: [`LogOS/API/Ports.agda`](LogOS/API/Ports.agda) with implementations under [`LogOS/Ports/`](LogOS/Ports/)
- Optional physics shell: [`LogOS/API/Ports/PhysicalOptional.agda`](LogOS/API/Ports/PhysicalOptional.agda) with curated submodules [`Causal`](LogOS/API/Ports/PhysicalOptional/Causal.agda), [`Landauer`](LogOS/API/Ports/PhysicalOptional/Landauer.agda), [`Deutsch`](LogOS/API/Ports/PhysicalOptional/Deutsch.agda), [`PreQuantum`](LogOS/API/Ports/PhysicalOptional/PreQuantum.agda)
- Adapters: [`LogOS/Adapters/`](LogOS/Adapters/)
- Application packs: [`LogOS/Apps/`](LogOS/Apps/)
- Curated APIs: [`LogOS/API/`](LogOS/API/)

Canonical orientation docs:

- Architecture diagram: [`docs/Core/Architecture/Diagram.lagda.md`](docs/Core/Architecture/Diagram.lagda.md)
- Layer order: [`docs/Generated/Architecture_Layer_Order.md`](docs/Generated/Architecture_Layer_Order.md)
- Repository capstones: [`docs/Core/Spec/LogOS_Specification.lagda.md`](docs/Core/Spec/LogOS_Specification.lagda.md)

## Tooling notes

This library ships `LogOS.agda-lib`.

- Repo-local invocation without global library setup:
  `agda --no-libraries -i . --safe --without-K -W all -W error LogOS/API/LT.agda`
- Toolchain sanity check:
  `make toolchain-check`
- Canonical library smoke lane:
  `make check-lib`
- Local library-file invocation using `LogOS.agda-lib` without global registration:
  `agda --no-default-libraries --library-file=_build/local.agda-libraries -l LogOS-LT --safe --without-K -W all -W error LogOS/API/LT.agda`
- If you have registered `LogOS.agda-lib` globally:
  `agda -l LogOS-LT --safe --without-K -W all -W error LogOS/API/LT.agda`

## License and citation

- License: GPL-3.0-only (`LICENSE`)
- Commercial licensing: contact `logos at ai-impact.com`
- Citation metadata: `CITATION.cff`

# SPDX-License-Identifier: GPL-3.0-only
