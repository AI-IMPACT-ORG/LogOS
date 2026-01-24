<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS: a platform for AI-driven, machine-verified, human-on-the-loop logical reasoning

The Agda library in this repository forms an effective development environment for human-AI collaboration to develop formal logical models and heterogeneous formal model networks as a formal logical model of basically anything that can be modelled ("coded") in software. It relies on some pretty fundamental and interesting mathematics, but can already be used today through coding agents for AI-driven, machine-verified, human-on-the-loop logical reasoning.

## Dive right in

Just download the library, ask your favorite code assistant (Codex, Claude Code, OpenCode, Cursor, etc.) to familiarise itself with the content of the library folders as a priming prompt. Watch it churn. Then start exploring, learning and building. Falsification is your friend: try to push hard against logical models to try to make them fall - this is the fastest route to improvement. 

A word of warning: LLMs become generally more coherent, but also sometimes more unstable for concentrated logic due to the presence of contextualised homonimy and polysemy in their training data. As a result, they confuse "literally" and "analogously", more or less like a human could. The logic literature on the other hand is perhaps the most coherent data source on the planet. The guardrails mentioned below have been designed to safely and incrementally increase information coherence and consistency inside the repository.


## High level overview

Models are typically expressed in dedicated domain-specific formal languages, which makes interoperability across domains and communities difficult. We demonstrate a scalable architecture for dynamic networks of heterogeneous logic systems that targets translations between formal models, leveraging software engineering methods operationalized by AI. This "inter-logics" architecture is inherently self-referential as it treats boundaries of logical systems as logical systems, formalised into ports and adapters and an operating-system analog for "kernels". The architecture distinguishes carefully between equal, equivalent and "equal under assumptions". The latter is an effective definition of "guarded truth" as "stability under resource-constrained interactions". 

We prove this logic system is sufficient to state and prove a generalisation of the classical Curry-Howard-Lambek correspondence between classical logic, type theory and category theory under a mild budgeted adequacy assumption to general symbolic "reasoning" under constraints. We showcase a semantics partially aligned with known links between physics and information theory based on the same kernel. 

We demonstrate the power of the approach with curated application packs: ZF(C) set theory via a well-founded membership-graph semantics, computational universality as **executable universal logic** (via scheme presentations and observational equivalence), and heterogeneous networks of bounded, self-improving agent models, among other results. Our results provide a foundational logic connecting different domains of science through their shared internal logic. This strongly supports an effective AI-powered consilience through controllable, formal-methods based engineering that seems profoundly powerful.

What seems to have happened is that the same set of ideas covered in this repository has been formalised several times in several domains. Church & Turing, Curry-Howard, Lawvere, universal logic, Deutsch's work: they all resonate strongly and are formalised to an extent inside the library. What is novel here as an idea is to apply modern software architecture and engineering patterns to foundational logic. The precise synthesis highlighting parallels and especially differences seems to be new.


## Guardrails for AI-assisted development

The epistemic status of the repository is somewhat unusual due to extensive use of coding agents. On the one hand, it contains very little human input channeled through people who are certainly not academic experts in *all* of the scientific areas the code touches (#understatement). On the other side, it is verified to a standard that is rare in academia through machine-checked code and a very broad variety of re-derivations and formalisations of known results. In this section we show which guardrails have been deployed to guarantee a measure of epistemic safety.

### Agda
Agda is a dependently typed programming language with tooling to act as a proof assistant. It is an extension of the  programming language Haskell (named after Haskell Curry), and can actually use that as a backend. Agda comes with some options for levels of type checking. We use the following compiler flags: 

- —W all —W error : all warnings turned on, all warnings are halting error for some measure of code quality.
 - —safe : turns of “pragmas” for placeholders inside Agda. This prevents AI from some forms of vacuous programs. This flag is set at the file level. - —no-libraries : we aim for a barebones logic system

### Continuous Integration
We use a continuous integration approach where after each major code change the whole codebase is checked by agda, and some manual checks for code issues we surfaced in real life are performed. This is also visible in the GitHub repository: every upload triggers a CI run that verifies that the code compiles in Agda. Several small scripts scan for failure patterns.

### Software Quality
Architecture and code quality are continuous concerns. We take the view that we rather solve explicit coding issues based on domain concerns than impose a rigid architecture.  In this repository code quality concerns correlate with particular concerns in mathematics of information science. To make this work we refactor often, including breaking refactors. A key goal is to keep the codebase as small as possible. Coding agents tend to prefer new development over reworking older parts - the user has to steer (hard) against this, otherwise spaghetti code is the result. 

Code architecture reviews are used to identify larger issues. A core pattern we use are ports and adapters from hexagonal architecture (See Cockburns blog). The original motivation for this was isolating logic inside code components, which is exactly what we use this for here. We use it especially to separate “kernels” from “applications” for foundational logic.

A key insight to operationalise this is to let the agent focus on inconsistencies, instead of asking it to make things consistent. The latter invites hallucinations. The first almost always finds something actionable. A clear sign of convergence is when the coding agent, after several rounds of improvements starts to focus only on the documentation. An interesting prompt is to ask to identify “bad code smells” or “bad architecture smells”. This works as it points the chatbot to the “refactoring to patterns” framework. Asking for focussed code improvements also works, as long as the agent gets some idea of where to push towards. The operator remains responsible for the vision and supervision. 

### Multipassing
An underrated technique to get a coding agent to perform larger scale operations to the end is to simply ask for the same thing several times. This resembles multi-passing for code optimisation for compiler. A variant of this involves resetting the coding agents memory, basically simulating getting a fresh “peer reviewer” to get a look. A more involved variant of multi-passing requires humans asking questions any developer would be asked by product owners, e.g. questions of performance, security and reliance. Regular architecture reviews using SOTA deep research is also part of a wider safety net.

### Documentation
We employ documentation-as-code. There is a special file format for mixtures of text and code called literate Agda, by the file extension .lagda. We use this to institute some integration checking, as well as semantic scaffolding for the coding agents to have a “big picture” to orient along. A fair portion each cycle is spend removing inconsistencies from the documentation. 

### Literature
We view existing literature as part of the wider safety net for especially scientific models. Especially important “textbook” results are useful as they are reflected deeply into the training corpus of chatbots. This is noticeable as chatbots tend to revert to the original, older literature somewhat over newer results. To surface newer results one typically has to dig deeper. We use literature results partly as a class of “integration tests” that fail when a breaking change hits.  

There are many links to the literature. Some concepts for this repository are especially the Curry-Howard-Lambek correspondence, the idea of "universal logic", Futumura's projections, Lawvere's fixed point theorem, the holographic renormalisation and renormalisation theory, especially the Connes-Kreimer variant. We have used these partly as goals, partly as analogs. See however the Limitations below.

### The Operator
The operator of a coding agent has in this framework the role as the ultimate arbiter of architecture and truth. In practice this is mostly steering, with exceptions when a hard decision has to be made. These hard decisions get less the clearer the framework becomes inside the repository. Also, the coding agent can help clarify decision parameters and, to an extend, impact on the codebase. 

### Limitations to guardrailing

No guardrailing on a software system of this level of complexity is perfect. The current speed of safe development bottleneck seems to be the ability of an operator to learn about this system and push through the resulting refactors. 

The biggest risk remaining is that of semantic divergence: the code not doing what the documentation says that its doing. By compartimenatilising concerns through architecture this is mitigated and blast radii reduced, but it is certainly not eliminated. This can only be fixed by external semantic peer-review. 

The list of links to concepts in the literature should be seen as a list of suggestions for further validation. 


## Repository overview


This entire library as well as its documentation was largely generated by AI and checked by AI - it contains a proof of concept of its own use. Among its guardrails are extensive CI, a novel logic architecture and an extensive documentation, all implemented in the proving language Agda and aligned to reduce hallucination impact. Tracking assumptions (axioms) carefully is a core feature.

It is an open problem if the semantics of the documentation *exactly* fits the syntax of the code, as some of the particular applications provided would require community verified re-axiomatisation of entire scientific fields, in particular physics. This is left as an exercise to the reader ( :) ) . For more targeted scope models that do not leverage the extreme coherence of the logic literature it is strongly recommended to verify results using human expertise.

Top usage tips: Always ensure good coding architecture (clean code, clean architecture for starters) in any new model for optimal results. Refactor almost constantly for presentation, and double and triple check results, ideally resetting chatbot memory to mitigate confirmation bias. Ask for better integration of kernel functions - their use is not always optimal downstream, especially if the result you are after is not in the literature. Best results are obtained usually with SOTA reasoning models, but these come with a hefty cost of time. Note that developments that align with classic literature are noticeably easier as the coding agents roughly know what to build. Directions perpendicular to the knowledge coded into the chatbots require more human supervision.

The main documentation lives in `/docs`. Uploading `docs/Definition_Spec.lagda.md` or almost any of the other docs to a reasoning chatbot instantiates a conversational interface to start exploring the library. This uses the chatbot as an effective stochastic interpreter. Ensure that memory features of the chatbot are disabled to avoid polluting cross-conversation chatbot memory. For bonus points: ask the chatbot to use the library to explain why this tip works based on a density of information argument. Beware of sycophancy induced by logic: not all suggestions as "next steps" are achievable in finite time, or require technology you have to learn first. 


## Some features

Requirements: Agda `2.7.0.1`.

```sh
# Type-check the minimal API (no global libraries needed)
agda --no-libraries -i . LogOS/API/Minimal.agda

# Run policy checks + vacuity/correctness checks + tests + docs
make ci
```

Optional publication sanity (heavier):

```sh
make check-all
```

Minimal “hello import”:

```agda
module Hello where
open import LogOS.API.Minimal
```

## Docs

Start here (literate Agda):
- Architecture + entrypoints: `docs/Definition.lagda.md`
- Research-grade spec: `docs/Definition_Spec.lagda.md`

Kernel views (polymorphicity): 
- Multi-institution: `docs/Views/MultiInstitution.lagda.md`
- 3-level HoTT-style: `docs/Views/HoTT_3Level.lagda.md`
- Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
- Observer semantics: `docs/Views/ObserverSemantics.lagda.md`
- Curry-Howard-Lambek capstone: `docs/Views/CurryHowardLambek.lagda.md`

Applications:
- ZFC story: `docs/Applications/ZFC.lagda.md`, `docs/DeepDive/ZFC_Demo.lagda.md`
- Complexity story: `docs/DeepDive/Complexity.lagda.md`, `docs/Applications/Complexity.lagda.md`
- Universality story: `docs/Applications/Universality.lagda.md`, `docs/Library.lagda.md`
- Opacity story (observability ledgers + no‑total‑oracle theorems): `docs/Applications/Opacity.lagda.md`
- Agents story: `docs/Applications/Agents.lagda.md`
- Conditional applications: see the relevant application notes under `docs/`

HTML docs (Agda HTML backend):
- Build locally: `make html` → `_build/html/index.html`

## Entry Points

Recommended import surfaces:
- Minimal API: `LogOS/API/Minimal.agda`
- LogicKernel API (CHL unified interface): `LogOS/API/LogicKernel.agda`
- Architecture map (ports/adapters spine): `LogOS/API/Architecture.agda`
- QAdapter instances: `LogOS/QAdapters/All.agda`
- Core theorem surface: `LogOS/Theorems/Core.agda`
- Transpiler pass calculus: `LogOS/Theorems/Meta/Transpiler.agda` (operational layer: `LogOS/Theorems/Meta/Transpiler/Operational.agda`)
- Bootstrapping: `LogOS/Theorems/Meta/Bootstrapping.agda`
- ZFC (stable): `LogOS/Packs/ZFC/All.agda` (WFGraph quartets: `LogOS/Packs/ZFC/WFGraph.agda`)
- UniversalIR (stable): `LogOS/Packs/UniversalIR/Core.agda`
- Universality bundle (stable): `LogOS/Packs/Universality/All.agda`
- Universality core (stable): `LogOS/Packs/Universality/Core.agda`
- Complexity (experimental): `LogOS/Packs/Complexity/Experimental/Core.agda`
- Opacity (experimental): `LogOS/Packs/Opacity/Experimental/Core.agda` (kernel-derived observability + barrier theorems)
- InfoTheory (stable): `LogOS/Packs/InfoTheory/Core.agda`
- Agents (stable): `LogOS/Packs/Agents/All.agda` (meta-language: `LogOS/Packs/Agents/MetaLanguage.agda`)
- Agents (experimental): `LogOS/Packs/Agents/Experimental/All.agda`

## Trust Boundary

- The safe core is intended to be imported via `LogOS/API/Minimal.agda` and contains no global postulates.
- Models that need ω‑chain suprema supply them explicitly via `LogOS/Axioms/OmegaSup/Interface.agda` (`ChainSup`) and `omegaCPO-from-chainSup`.
- Pack surfaces export `packTrust : PackTrust` (see `LogOS/Packs/Trust.agda`) to flag `stable`/`experimental`/`scaffold`/`deprecated`.
- CI enforces pack-trust metadata via `make pack-trust-check` (included in `make ci-policy` / `make ci`).
- Experimental surfaces are under evaluation and should be considered less stable than the rest of the repository.
- This repo does not claim classical proofs of famous conjectures (e.g. GRH/RH, P vs NP). Those strands are modeled as conditional ledgers and proof templates that isolate minimal assumptions (reverse mathematics), and are interesting even without new classical proofs.
- This repository is AI-generated; use the Agda checker and the stated trust levels as your primary guardrails.

Host surface (portability):
- Direct imports from `Agda.Primitive` / `Agda.Builtin.*` are intentionally restricted to a small allowlist:
  - `Data/Level.agda`
  - `Data/Nat.agda`
  - `Data/Bool.agda`
  - `Data/List.agda`
  - `Data/Maybe.agda`
  - `Data/String.agda`
  - `Data/Relation/Binary/PropositionalEquality.agda`
- CI enforces this via `make host-surface-check` (included in `make ci`).

## Build Targets

- `make ci` — policy checks + tests + docs
- `make vacuity-check` — vacuity guard surfaces (non‑vacuous claims)
- `make correctness-check` — correctness surfaces (soundness/adequacy)
- `make packs` — type-check curated packs
- `make html` — build HTML docs into `_build/html/`
- `make check-all` — type-check every `*.agda` and `*.lagda.md` with `-W all -W error`

## License and Citation

- License: GPL-3.0-only (`LICENSE`)
- Citation metadata: `CITATION.cff`

<details>
<summary>Agda library setup (optional)</summary>

This library ships `LogOS.agda-lib`.

- Register in your global libraries file (e.g. `~/.agda/libraries`), then:
  - `agda -l LogOS LogOS/API/Minimal.agda`

Local setup note (library trouble):
- Quick fix: use `agda --no-libraries -i . LogOS/API/Minimal.agda` (no global config needed).
- If you prefer `-l LogOS` without touching `~/.agda/libraries`, create a repo-local
  `local.agda-libraries` file with the full path to `LogOS.agda-lib`, then run:
  `agda --library-file=local.agda-libraries -l LogOS LogOS/API/Minimal.agda`.

Using alongside agda-stdlib:
- This codebase ships minimal `Data.*` shims so it can build without stdlib.
- If you want to use agda-stdlib in the same project, prefer importing LogOS via the API modules and avoid mixing raw `Data.*` names.

</details>

<details>
<summary>Tensor / Endomap DSL (boundary-level “process calculus”)</summary>

This repo exposes a conservative DSL over monotone boundary endomaps:

- `LogOS/Kernel/TensorDSL.agda` (also re-exported by `LogOS/API/Minimal.agda`)
- Canonical fixed-point surface: `Th⋆K`, `FlowTh⋆K`, `Th⋆≤FlowTh⋆`, `FlowTh⋆≤Th⋆`
- Note: the kernel record field is `Th*`; the `Th⋆…` names are the same witness exposed as endomap-DSL aliases.
- Antisymmetry upgrade: `FlowTh⋆≡Th⋆` (alias: `fixedpoint-eq-under-antisym`)

</details>

<details>
<summary>Meta theorems quickstart (Rice/Tarski/Gödel/Löb shape)</summary>

The `LogOS/Theorems/Meta/*` namespace contains assumption-based theorem schemas. Transport is via the canonical fold:

- Assumptions: `LogOS/Theorems/Meta/Assumptions/Core.agda`, `LogOS/Theorems/Meta/Assumptions/Diagonal.agda`
- Core provability ops (kernel-independent `*C` records): `LogOS/Theorems/Meta/Assumptions/Core.agda`
- Transport: `LogOS/Theorems/Meta/Full.agda`
- Wrappers: `LogOS/Theorems/Meta/Rice.agda`, `LogOS/Theorems/Meta/Tarski.agda`, `LogOS/Theorems/Meta/Godel.agda`, `LogOS/Theorems/Meta/Lob.agda`
- CHL (Curry-Howard-Lambek) theorems: `LogOS/Theorems/Meta/CHL/` (capstone, completeness, model theory, proof theory)

</details>

<details>
<summary>Compilation and Transpilation</summary>

The library includes compilation and transpilation capabilities:

- Transpiler: `LogOS/Theorems/Meta/Transpiler.agda` with operational semantics in `LogOS/Theorems/Meta/Transpiler/Operational.agda`
- Bootstrapping support: `LogOS/Theorems/Meta/Bootstrapping.agda`
- Agent backends: Python (`LogOS/Packs/Agents/Emit/Backends/Python/`) and TensorFlow (`LogOS/Packs/Agents/Experimental/Emit/Backends/TensorFlow/`)
- IR backend: `LogOS/Packs/Agents/Emit/IR/` for intermediate representation

</details>
