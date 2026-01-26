<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS: an Agda library for logic-system architecture (ports/adapters)

This repository contains **LogOS**, a host-minimal Agda library that treats “logic
systems” as interface-bearing components in a network, with explicit
ports/adapters for translation and interoperability. The primary guardrail is
the Agda checker plus a CI/policy harness (`make ci`, `make check-all`).

## Dive right in

Just download the library, ask your favorite code assistant (Codex, Claude Code, OpenCode, Cursor, etc.) to familiarise itself with the content of the library folders as a priming prompt. Watch it churn. Then start exploring, learning and building. 

A word of warning: LLMs become generally more coherent, but also occasionally more unstable for concentrated logic due to the presence of contextualised homonymy and polysemy in their training data. The coherence originates in the extreme coherence of the logic literature across papers. The guardrails mentioned below have been designed to safely and incrementally increase information coherence and consistency inside the repository. 

To set expectations: this repository is the result of several *months* worth of COTS inference compute, mostly spent in dialog and mostly spent on correcting previous results. This is science, do not expect magic, even if it feels like it. On the other hand, the power of limitations seems larger than usually appreciated. 

## High level overview

Models are typically expressed in dedicated domain-specific formal languages,
which makes interoperability across domains and communities difficult. LogOS
focuses on an explicit translation architecture: boundaries are first-class, and
translations are forced/unique when two presentations share the same boundary
meaning (up to satisfaction).

Wording discipline (guardrail)
------------------------------
The docs try to distinguish four kinds of statements:

- **Literal (checked):** an Agda definition/lemma in the referenced file.
- **Truth after computation (stabilized):** a statement about a closure/fixed
  point (e.g. `Th*`, `Box`, `μ Flow`); by default this is only a *lax* fixed
  point unless ω‑sup/continuity assumptions are supplied.
- **Representational truth (presentation):** a statement transported through
  `decode`/`encode`/`translate`/`SatMor`, i.e. preserved up to the relevant
  satisfaction equivalence; this is not definitional equality.
- **Analogy / interpretation:** explanatory metaphors (kernel, channel, RG,
  “GRH”, …). These are explicitly marked as interpretations and never add
  logical power; the formal content is always the cited Agda surface.

The library includes a Curry–Howard–Lambek–shaped theorem bundle for its internal
`LogicKernel` interface. Soundness is literal (checked); completeness-style
statements are available only under explicit adequacy assumptions (see
`docs/Views/CurryHowardLambek.lagda.md`).

The repository contains curated application packs (with explicit trust levels via
`packTrust`), including ZF(C) set theory, computational universality via
UniversalIR, information theory interfaces, and conditional “ledger” packs for
opacity (GRH/RH-shaped) and complexity (P/NP-shaped). No classical proofs of GRH
or P≠NP are claimed; those strands are packaged as conditional assumptions +
reverse-mathematics templates.

Interpretation note: the docs sometimes point to classical literature as
inspiration (Curry–Howard–Lambek, Lawvere fixed points, universality, etc.). Such
links are analogies/scaffolding; the only claims are the ones typechecked in the
library under stated assumptions.


## Guardrails for AI-assisted development

The epistemic status of the repository is somewhat unusual due to extensive use of coding agents. On the one hand, verifying all of these results requires a full research university worth of experts - this verification has not taken place yet (#understatement). On the other hand, it is verified to a standard that is very rare in academia or in industry through machine-checked code and a very broad variety of re-derivations and formalisations of known results. In this section we briefly show which guardrails have been deployed to guarantee epistemic safety, and indicate some limitations.

### Agda
Agda is a dependently typed programming language with tooling to act as a proof assistant.
Agda comes with some options for levels of type checking. This repo uses:

- `-W all -W error` — all warnings turned on; warnings are treated as errors.
- `--safe` — disallow unsafe pragmas/placeholders (still relative to the Agda checker).
- `--no-libraries -i .` — build without stdlib (host-minimal surface).

### Continuous Integration
CI runs `make check-all` (policy checks + full typecheck of all `*.agda` and
`*.lagda.md`) plus a library-file smoke test (`make agda-lib-check`). See
`.github/workflows/ci.yml`.

### Software Quality
Architecture and code quality are continuous concerns. We take the view that we rather solve explicit coding issues based on domain concerns than impose a rigid architecture.  In this repository code quality concerns correlate with particular concerns in mathematics of information science. To make this work we refactor often, including breaking refactors. A key goal is to keep the codebase as small as possible. Coding agents tend to prefer new development over reworking older parts - the user has to steer (hard) against this, otherwise spaghetti code is the result. 

Code architecture reviews are used to identify larger issues. A core pattern we use are ports and adapters from hexagonal architecture (See Cockburn's blog). The original motivation for this was isolating logic inside code components, which is the role we use it for here. We use it especially to separate “kernels” from “applications” for foundational logic.

A key insight to operationalise this is to let the agent focus on inconsistencies, instead of asking it to make things consistent. The latter invites hallucinations. The first almost always finds something actionable. A clear sign of convergence is when the coding agent, after several rounds of improvements starts to focus only on the documentation. An interesting prompt is to ask to identify “bad code smells” or “bad architecture smells”. This works as it points the chatbot to the “refactoring to patterns” framework. Asking for focussed code improvements also works, as long as the agent gets some idea of where to push towards. The operator remains responsible for the vision and supervision. 

### Multipassing
An underrated technique to get a coding agent to perform larger scale operations to the end is to simply ask for the same thing several times. This resembles multi-passing for code optimisation in compilers. A variant of this involves resetting the coding agents memory, basically simulating getting a fresh “peer reviewer” to get a look. A more involved variant of multi-passing requires humans asking questions any developer would be asked by product owners, e.g. questions of performance, security and reliance. Regular architecture reviews using SOTA deep research is also part of a wider safety net.

### Documentation
We employ documentation-as-code. There is a special file format for mixtures of text and code called literate Agda, by the file extension .lagda. We use this to institute some integration checking, as well as semantic scaffolding for the coding agents to have a "big picture" to orient along. A fair portion each cycle is spent removing inconsistencies from the documentation. 

### Literature
We view existing literature as part of the wider safety net for especially scientific models. Especially important “textbook” results are useful as they are reflected deeply into the training corpus of chatbots. This is noticeable as chatbots tend to revert to the original, older literature somewhat over newer results. To surface newer results one typically has to dig deeper. We use literature results partly as a class of “integration tests” that fail when a breaking change hits.  

There are many, many links to the literature. Some concepts relevant for this repository are especially the Curry-Howard-Lambek correspondence, the idea of "universal logic", Futamura's projections, Lawvere's fixed point theorem, holographic renormalisation and renormalisation theory, especially the Connes-Kreimer variant, Analytic S-matrix theory as well as basic notions of quantum mechanics. We have used these partly as goals, partly as analogs and throughout as scaffolding to find the next refinement.

### The Operator
The operator of a coding agent has in this framework the role as the ultimate arbiter of architecture and truth. In practice this is mostly steering, with exceptions when a hard decision has to be made. These hard decisions get less the clearer the framework becomes inside the repository. Also, the coding agent can help clarify decision parameters and, to an extent, impact on the codebase. 

### Limitations to guardrailing

No guardrailing on a software system of this level of complexity is perfect. The current speed of safe development bottleneck seems to be the ability of an operator to learn about this system and guide through the resulting refinement options. 

The biggest risk remaining is that of semantic divergence: the code not doing what the documentation says that its doing. By compartmentalising concerns through architecture this is mitigated - agents can check module-by-module. The loose coupling through ports and adapters also greatly reduces blast radii. AI-driven reviews have diminishing returns in their current state - the meaning of the system is largely approaching stability. Ultimately this remaining risk can only be fixed fully by external semantic peer-review. 

A final risk is the Agda compiler itself - although this is not a green-fields development, soundness and consistency proofs in Agda code are only relative to the Agda compiler.


## Repository overview

The main documentation lives in `/docs`. Uploading `docs/Definition_Spec.lagda.md` or almost any of the other docs to a reasoning chatbot instantiates a conversational interface to start exploring the library. This uses the chatbot as an effective stochastic interpreter. Ensure that memory features of the chatbot are disabled to avoid polluting cross-conversation chatbot memory. For bonus points: ask the chatbot to use the library to explain why this tip works based on a density of information argument. Beware of sycophancy induced by logic: not all suggestions as "next steps" are achievable in finite time, or require technology you have to learn first. 

## Usage tips

Interpretation (analogy): you can view the library as an “OS-style” abstraction
for composing logic-system components (kernels + ports + adapters). The literal
content is the Agda API and the curated packs.

Always ensure good coding architecture (clean code, clean architecture for starters) in any new model for optimal results. Refactor almost constantly for presentation, and double and triple check results, ideally resetting chatbot memory to mitigate confirmation bias. Ask for better integration of kernel functions - their use is not always optimal downstream, especially if the result you are after is not in the literature. Best results are obtained usually with SOTA reasoning models, but these come with a hefty cost of time. Note that developments that align with classical literature are noticeably easier as the coding agents roughly know what to build. Directions perpendicular to the knowledge coded into the chatbots require more human supervision.

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
- Kernel claim register (what “truth” words mean): `docs/Kernel/ClaimRegister.lagda.md`
- Research-grade spec: `docs/Definition_Spec.lagda.md`

Kernel views (polymorphicity): 
- Multi-institution: `docs/Views/MultiInstitution.lagda.md`
- 3-level HoTT-style: `docs/Views/HoTT_3Level.lagda.md`
- Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
- Observer semantics: `docs/Views/ObserverSemantics.lagda.md`
- Curry-Howard-Lambek capstone: `docs/Views/CurryHowardLambek.lagda.md`
- Meredith sentences (ultra-compact core math): `docs/Views/MeredithSentences.lagda.md`

Applications:
- ZFC story: `docs/Applications/ZFC.lagda.md`, `docs/DeepDive/ZFC_Demo.lagda.md`
- Complexity story: `docs/DeepDive/Complexity.lagda.md`, `docs/Applications/Complexity.lagda.md`
- Universality story: `docs/Applications/Universality.lagda.md`, `docs/Library.lagda.md`
- Opacity story (observability ledgers + no‑total‑oracle theorems): `docs/Applications/Opacity.lagda.md`
- InfoTheory story (Shannon + DPI/Capacity/ThermoRG): `docs/Applications/InfoTheory.lagda.md`
- Agents story: `docs/Applications/Agents.lagda.md`
- Conditional applications: see the relevant application notes under `docs/`

HTML docs (Agda HTML backend):
- Build locally: `make html` → `_build/html/index.html`

## Entry Points

Recommended import surfaces:
- Minimal API: `LogOS/API/Minimal.agda`
- LogicKernel API (CHL unified interface): `LogOS/API/LogicKernel.agda`
- Architecture map (ports/adapters spine): `LogOS/API/Architecture.agda`
- One-page architecture diagram: `docs/Architecture_Diagram.md`
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
  - `LogOS/Host/Level.agda`
  - `LogOS/Host/Nat.agda`
  - `LogOS/Host/Bool.agda`
  - `LogOS/Host/List.agda`
  - `LogOS/Host/Maybe.agda`
  - `LogOS/Host/String.agda`
  - `LogOS/Host/Relation/Binary/PropositionalEquality.agda`
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
- This codebase ships a minimal host surface so it can build without stdlib.
- LogOS uses namespaced host wrappers under `LogOS/Host/*` (re-exported via `LogOS.Prelude` / `LogOS.Prelude.*`).
- If you want to use agda-stdlib in the same project, prefer importing LogOS via the API modules and avoid mixing stdlib `Data.*` modules into the LogOS core.

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
