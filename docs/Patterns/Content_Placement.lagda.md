<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: content placement (theorems vs docs vs packs)

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Content_Placement where

import LogOS.API.LT
```

LogOS aims to keep the LT core minimal and host-minimal. That only works if we keep a
sharp separation between:

- **structure** (kernel/ports; reusable proof patterns), and
- **story** (domain dictionaries, “how to read this”, relabellings), and
- **case studies** (packs that instantiate the structure).

This document states the placement policy and the CI checks that enforce the
mechanical parts.

## Taxonomy (spine vs ports vs views vs apps)

LogOS uses the word “core” in a deliberately layered way. The shortest useful
taxonomy is:

- **Spine (atomic, import-minimal)**: the meaning-carrying nucleus.
  - Concretely: the atomic LT spine modules (`ConPreorder`, `View`, `Kernel`,
    `Hom`, `Thin2Cat`, `Thin2Functor`, `DisplayedThin2Cat.*`).
  - Design stance: *local refinement first*; avoid collapsing to global equality.
- **Taxonomy (LT derived, still meaning-preserving)**: reusable structure built
  on the spine without adding new kernel axioms.
  - Examples: `LOG`, `Contracts`, `Presentation`, `Reflection`, `Flow/Iteration`,
    port stacking (`PortSig`/`PortStack`), and a small amount of genuinely
    spine-level theorem tooling.
- **Ports (displayed layers)**: architectural interfaces and obligations, always
  formulated as displayed structure over a base thin 2-category.
  - Concretely: `LogOS/Ports/**` and `LogOS/LT/LOG/*2Cat.agda`.
- **Views / interpretations (emergent)**: optional packagings that read the
  spine as familiar textbook structures (institution fragments, predicate
  reindexing fragments, derivability layers,
  etc.). These are *not* part of the default curated surface.
- **Adapters**: concrete morphisms between kernels (and between port-stacked
  objects), living under `LogOS/Adapters/**`.
- **Apps**: downstream instantiations (ledgers/decks + showcases), living under
  `LogOS/Apps/**`.

Hard design rule (enforced by policy checks):

- The **spine must not import** views/apps/adapters.
- **Strictness never becomes ambient**: extensionality principles and
  strict equalities are only available via explicit, opt-in layers (ports).

### Type tower (spine → ports → stacks)

The folder taxonomy above is backed by a compact “tower” of types that are designed to interlock.
In order (each step builds on the previous):

1. `ConPreorder` (refinement kit): the carrier of observable constraints (`⊑`, `≈`, monotone maps).
2. `View` (presentation discipline): a named observation map and induced pullback refinements.
3. `Kernel` (transformer): code + boundary + decoding (`Code`, `bnd`, `decode`).
4. `BoundaryHom` (boundary-transport 1-cells): monotone boundary transport (`map∂` + monotonicity).
5. `BoundaryImplementation` / `KernelHomLike` (implementation-tier displayed layer): an implementation witness (`implementCode`) plus mode-polymorphic coherence
   (`decode-mapCode : CohRel m … …` with `m ∈ {strict, approx, under}`).
6. `LOGᴳ` (boundary-only base 2-category): boundary morphisms with 2-cells refining *pure transport* (pointwise on all boundary constraints).
7. `DisplayedThin2Cat` (ports): extra object/morphism payload and obligations over a base thin 2-category, with refinement inherited from the base.
8. `PortSig` / `PortStack` (stacking + structural subtyping): tagged displayed layers, product-stacking, and typed projections/forgetting by capabilities.
9. `DecoratedThin2Cat` (totalisation): Σ-totalisation of displayed structure into a new thin 2-category.

Two boundary-driven refinements are intentionally distinguished:

- In `LOGᴳ`, refinement is pointwise on **all** boundary constraints (pullback along the boundary transport view).
- In base `LOG`, refinement is pointwise on **transported decoded codes** (`transportView` / `_⇒∂_`).
  The implementation-first picture (`obsView` / `_⇒_`) is pointwise `≈`-equivalent, and is treated as an explicit derived convenience (`ImplementationView`), not as the flat default surface.

Strictness discipline:
any collapse from `≈` to `≡` (either for decode coherence or for boundary equality) is only available behind explicit,
opt-in layers/ports (e.g. `StrictDecode`, `ClassicalLimit`), never as ambient structure in the spine.

### Interlocking types (what enforces the taxonomy)

The taxonomy above is not only a folder convention; it is encoded by a short set of types that “lock”
the design together:

- **Boundary refinement kit**: `ConPreorder`, `_⊑_`, `_≈_`, `MonoMap` (`LogOS/LT/ConPreorder.agda`).
- **Meaning injection**: `View` and pullback refinement (`LogOS/LT/View.agda`).
- **Kernel transformer**: `Kernel` (`bnd`, `Code`, `decode`) (`LogOS/LT/Kernel.agda`).
- **boundary transport layer**: `BoundaryHom` (`map∂` + monotonicity) (`LogOS/LT/BoundaryHom.agda`).
- **implementation tier (displayed witnesses)**: `BoundaryImplementation approx` (`implementCode` + `decode-implementsBoundary : _≈_`) and
  `KernelHom = Σ BoundaryHom (BoundaryImplementation approx)` (`LogOS/LT/Hom.agda`, `LogOS/LT/BoundaryImplementation.agda`).
- **Boundary-only base 2-category** (boundary/base vs displayed-implementation split):
  - `LOGᴳ`: kernels with 1-cells `BoundaryHom` (level-aligned via `BoundaryHomL`) and 2-cells refining *pure boundary transport*
    (pointwise on boundary constraints) (`LogOS/LT/LOG/Boundary2Cat.agda`).
  - `LOGᴳʳ`: Σ-totalisation adding implementation witnesses as a displayed layer (`BoundaryImplementation approx`), plus the weakening functor `toLOG`
    to recover the usual `LOG` refinement (`LogOS/LT/LOG/Implementation2Cat.agda`).
- **Port reindexing across bases** (LOG-basis port → LOGᴳʳ-basis port):
  strict pullback along `toLOG` (via `reindexDisplayedStrictF (toLOGStrict …)` or the packaged helpers
  `pullbackPortSigAlongToLOG` / `pullbackPortEntryAlongToLOG` / `pullbackPortStackAlongToLOG`) and the canonical
  weakening functor back to the LOG-basis (`weakenDecoratedAlongToLOG`) (`LogOS/LT/LOG/PortReindexing/Strictification.agda`).
- **Exemplar stack over `LOGᴳ`**: `LOGᴳʳ∂` (implementations + contracts as a `PortStack`, with a weakening functor back to the contract port category `LogOS.LT.LOG.Contract2Cat.WithPort`)
  (`LogOS/LT/LOG/ImplementationContract2Cat.agda`).
- **One canonical and one derived 2-cell presentation**: boundary-driven `transportView`/`_⇒∂_` is canonical; implementation-first `obsView`/`_⇒_` is retained as the derived view
  (base `LOG` uses `_⇒∂_`) (`LogOS/LT/Hom.agda`, `LogOS/LT/LOG/Kernel2Cat.agda`).
- **Coherence “subtyping”** (explicit coercions): `strict→approx`, `approx→under` (`LogOS/LT/Hom/Coercions.agda`).
- **Ports as displayed layers**: `DisplayedThin2Cat`, `DecoratedThin2Cat` (`LogOS/LT/DisplayedThin2Cat.agda`).
- **Port stacks (structural subtyping)**: `PortSig`, `PortStack`, `HasPort`, `getObj`, `getHom`, `forgetPort`, `forgetSubstack`
  (`LogOS/LT/Ports/PortSig.agda`, `LogOS/LT/Ports/PortStack.agda`).
- **Explicit strictness checks** (never ambient): kernel-level strictification via `LogOS/Ports/ClassicalLimit.agda`,
  and stack-level strictification via `LogOS/LT/Ports/PortStack/ClassicalLimit.agda`.

## Placement rules (where things go)

### `LogOS/LT/Theorems/**` — prove once, reuse everywhere

Put something in `LogOS/LT/Theorems/**` iff it satisfies at least one:

- it is a **structural theorem** about kernels/ports/closure/translation that is
  expected to be reused across multiple packs, or
- it eliminates a **recurring proof pattern** (a “tooling loop”) you want to
  apply repeatedly in downstream code.

Do **not** put something in `LogOS/LT/Theorems/**` merely because it is
reusable somewhere. If the theorem vocabulary is inseparable from a chosen
interface story (for example, public/private observation loss, opacity
profiles, or other interpretation packs), keep that vocabulary with the pack
instead of advertising it as default-core LT mathematics.

If you add a new theorem module, it must be **catalogued** by exposing it
from the curated theorems API surface (`LogOS/API/Theorems/Core.agda` for
refinement-first results, `LogOS/API/Theorems/Strictification.agda` for
explicit equality/strictification results) (enforced in CI).

### `LogOS/Ports/**` — name interfaces + combinators

Ports exist to make architectural patterns first-class:

- interfaces (what is observed; what counts as refinement),
- combinators (how interfaces compose),
- minimal hypotheses (what is parameterised vs proved).

Ports should *not* duplicate genuinely generic spine theorems. But pack-local
theorem vocabularies that fundamentally depend on the chosen interface story are
supposed to stay with the pack rather than move into `LT/Theorems`.

Recent example of the placement rule:

- the only new LT seam is `LogOS/LT/View/Factorisation.agda`,
- factorisation/distinguishability/loss/readback obstruction now live in the
  optional opacity pack `LogOS/Ports/Opacity/**`,
- the derived finite-loss layer also lives in that pack
  (`LogOS/Ports/Opacity/FiniteCompression.agda`),
- the Landauer lower-bound bridge remains downstream in
  `LogOS/Ports/AbstractLandauerObservational.agda`,
- default curated surfaces do not advertise the opacity pack; it is exposed only
  through the explicit opt-in module `LogOS/API/Opacity.agda`.

### `LogOS/Apps/**` — ledgers/decks + showcases (domain-facing)

Application packs are where you:

- name **designer choices** (boundaries, closures, observation vocabularies),
- expose the **irreducible obligations** as records (the “math lives here” fields),
- provide **short end-to-end examples** that make the architecture concrete.

Apps are intentionally *not* part of the curated core API surface.

If you find yourself proving the same “routine in LogOS” lemma twice in Apps, move
it to `LogOS/LT/Theorems/**`.

Practical hygiene rule:

- Do **not** add README-only “planned packs” under `LogOS/Apps/**`.
- If a pack has no checked entrypoint yet, keep the intent in a `docs/**` design
  note, and create the pack directory only once it contains at least one
  `{-# OPTIONS --safe #-}` Agda module.

### `docs/**` — relabelling, dictionaries, reading guides

Docs are the right home for:

- “this classical word corresponds to this field” dictionaries,
- reformulations that do not introduce reusable lemmas,
- narrative bridges for domain experts.

If the doc needs compiler-checked anchors, prefer a `*.lagda.md` document.

## Decision workflow (quick checklist)

1. **Does it change what can be proved downstream?**
   - Yes → likely a theorem (`LogOS/LT/Theorems/**`) or a port.
2. **Is it a named architectural interface/combinator?**
   - Yes → port (`LogOS/Ports/**`).
3. **Is it domain narrative / “how to read” / relabelling?**
   - Yes → docs (`docs/**`).
4. **Is it a domain instantiation (ledger/deck) or a minimal end-to-end demo?**
   - Yes → app pack (`LogOS/Apps/**`).

## CI enforcement (what is checked)

The following checks enforce the mechanical parts of this policy:

- `layer-order-check`: keeps LT/Ports/Adapters/Apps/API import direction sane.
- `api-purity-check`: ensures `LogOS/API/**` imports only from Prelude/Syntax/LT/Ports/API
  (so the curated API cannot depend on Apps/Adapters).
- `doc-import-discipline-check`: public-facing `*.lagda.md` docs import `LogOS.API.LT`
  and avoid deep internal imports.
- `reachability-check`: every non-Host core module must be reachable from `LogOS.API.LT`
  and/or the spec-doc sync guards.
- `theorems-catalog-check` (added): every `LogOS/LT/Theorems/**/*.agda` file must be surfaced through
  `LogOS/API/Theorems/Core.agda` and/or `LogOS/API/Theorems/Strictification.agda`.

Terminology policy:

- `docs/Patterns/Terminology_Policy.lagda.md`
