<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Multi-Institution (Classic Model Theory)

```agda
{-# OPTIONS --safe #-}
module docs.Views.MultiInstitution where

-- Typechecked “view surface” for the multi-institution presentation.
--
-- Keep this module lightweight to avoid name clashes when imported alongside
-- other views/tests.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.API.Views as Views
open Views.Kernels using (Kernel)
import LogOS.API.Views.ModelTheory as ModelTheory

module ViewTheorems = Views.ViewTheorems
module StrictReindex = Views.StrictReindex
module ViewSatMor = Views.ViewSatMor
module Interoperability = Views.PortsAdapters.Interoperability

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = ViewTheorems.For K
  module MT = ModelTheory.For K
  open V.MultiInstitution public
  module Reindex = ViewTheorems.Reindex
  module ReindexWithFml = ViewTheorems.ReindexWithFml
  module ReindexingSatisfaction = ViewTheorems.ReindexingSatisfaction
  module ReindexingSatisfactionWithFml = ViewTheorems.ReindexingSatisfactionWithFml
  module ReindexingSatisfactionWithFmlLogic = ViewTheorems.ReindexingSatisfactionWithFmlLogic

  private
    coh-SH-exists : _
    coh-SH-exists = coh-SH

    coh-H∂-exists : _
    coh-H∂-exists = coh-H∂

    layer-coh-SH-exists : _
    layer-coh-SH-exists = MT.LayeredInstitution.coh-SH

    layer-coh-H∂-exists : _
    layer-coh-H∂-exists = MT.LayeredInstitution.coh-H∂

    rename∂-exists : _
    rename∂-exists = SentenceLayer.rename∂

    rename∂-id-exists : _
    rename∂-id-exists = SentenceLayer.rename∂-id

    rename∂-compose-exists : _
    rename∂-compose-exists = SentenceLayer.rename∂-compose

    interp∂-rename-exists : _
    interp∂-rename-exists = SentenceLayer.interp∂-rename

    module _ {Sig₁ Sig₂ : LogOSSignature ℓ}
             (σ : SigHom Sig₁ Sig₂)
             (K₂ : Kernel Sig₂ Q)
             where
      module RS₀ = ReindexingSatisfaction σ K₂

      SatS-precompose-exists : _
      SatS-precompose-exists = RS₀.SatS-precompose

      SatH-precompose-exists : _
      SatH-precompose-exists = RS₀.SatH-precompose

      SatHbnd-precompose-exists : _
      SatHbnd-precompose-exists = RS₀.SatHbnd-precompose

    module _ {Sig₁ Sig₂ : LogOSSignature ℓ}
             (σ : SigHom Sig₁ Sig₂)
             (K₂ : Kernel Sig₂ Q)
             {Fml₁ : Set ℓ}
             (mapFml : Fml₁ → Kernel.Fml K₂)
             where
      module RS₁ = ReindexingSatisfactionWithFml σ K₂ mapFml
      module SR = StrictReindex.ForKernel σ K₂ mapFml

      SatS-precompose-mapFml-exists : _
      SatS-precompose-mapFml-exists = RS₁.SatS-precompose

      translate≈mapFml-exists : _
      translate≈mapFml-exists = SR.translate≈mapFml

      mapFml-unique-exists : _
      mapFml-unique-exists = SR.mapFml-unique

    module _ {Sig₁ : LogOSSignature ℓ}
             (σ : SigHom Sig₁ Sig)
             {Fml₁ : Set ℓ}
             (mapFml : Fml₁ → Kernel.Fml K)
             where
      module RI = MT.RepresentationIndependence.ForStrictReindex σ mapFml
      module RC = MT.RelativeCompleteness.ForStrictReindex σ mapFml

      mapFml-unique-modelTheory-exists : _
      mapFml-unique-modelTheory-exists = RI.mapFml-unique

      complete-mapFml-exists : _
      complete-mapFml-exists = RC.complete-mapFml

    semantics-transport-comp-exists : _
    semantics-transport-comp-exists =
      MT.RepresentationIndependence.SemanticsTransport.translate-comp

    separation-diagonal-witness-exists : _
    separation-diagonal-witness-exists =
      MT.SeparationBoundary.separation-diagonal-witness

    budgeted-diagonal-witness-exists : _
    budgeted-diagonal-witness-exists =
      MT.SeparationBoundary.budgeted-diagonal-witness

    heteroCanonicalAdapter-exists : _
    heteroCanonicalAdapter-exists = Interoperability.heteroCanonicalAdapter

    heteroAdapter-unique-exists : _
    heteroAdapter-unique-exists = Interoperability.heteroAdapter-unique

    satMor-strict-to-boundary-exists : _
    satMor-strict-to-boundary-exists = ViewSatMor.satMor-strict-to-boundary

    satMor-code-to-boundary-exists : _
    satMor-code-to-boundary-exists = ViewSatMor.satMor-code-to-boundary

    projection-exists : _
    projection-exists = V.Projections.projection
```

Purpose
-------
This view presents the LogOS kernel in classic model-theoretic language, as a
multi-institution-shaped interface: multiple satisfaction relations (S/H/∂, and
optionally G/closure) linked by explicit coherence laws and explicit reindexing
along signature morphisms.

Two axes are kept explicit: reindexing along `SigHom` changes which satisfaction relation you talk about, while ports/adapters compare presentations of a fixed satisfaction relation.

It is intentionally “implementation-aligned”: where the Agda library does not
expose a notion as a packaged categorical structure (e.g. a `Category` record),
we make the weakest presentation consistent with the implemented interfaces.
In particular, this note sometimes works **at fixed signature** (so signatures
can be treated as the terminal category), while also pointing to the
nontrivial signature-change interfaces that *do* exist (`SigHom`, `reindexKernel`,
`reindexKernelWithFml`, and the optional `rename∂` sentence layer).

Interpretation (analogy):
this document is a derived presentation (“view”) over the same kernel interfaces;
it does not add logical power.

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
- Parameter: `Kernel Sig Q`.
- Surface: `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `MultiInstitution`).

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Signatures (objects) | `LogOSSignature` | Kernel parameter; not a global “category of all signatures” by default. |
| Signature morphisms | `SigHom` (`LogOS/Base/Signature/Hom.agda`) | Identity/composition available; enough for institution-style satisfaction conditions. |
| Sentences (`Sen`) | strict formulas `Fml`, optional boundary sentence layer `Con∂` + `rename∂` | `Sen` can be taken trivial-on-morphisms, or made nontrivial via `rename∂`/`mapFml`. |
| Models (`Mod`) | worlds/contexts `Cosp` (optionally a preorder via `_≤ctx_`) | Presented conservatively as discrete unless you assume `CtxPreorder`. |
| Satisfaction | `Sat_S`, `Sat_H`, `Sat_H_bnd` | Three-tier interface (S/H/∂) rather than a single `⊨`. `Sat_H w c` is world‑indexed; `Sat_H_bnd (to∂ w) c` is the boundary-indexed coherence. |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital prequantale in the finite-join sense (not complete); mostly orthogonal to the institution story. |
| Satisfaction condition | `Sat*-precompose` lemmas under reindexing | Implemented as literal precomposition in theorems (reindexing surface). |
| Inter-institution translations | ports/adapters, hetero canonical adapters | “Presentation independence” is a first-class boundary feature. |

Core definitions (literature style)
-----------------------------------

**Definition (Institution satisfaction condition, LogOS form).** Reindexing is
contravariant on models (`reindexKernel`) and (optionally) covariant on strict
sentences (`reindexKernelWithFml` / `mapFml`). The satisfaction condition is
presented in the library as explicit “precomposition” lemmas (`Sat*-precompose`)
rather than as a global categorical axiom.

**Definition (Multi-institution spine).** LogOS supplies multiple satisfaction
relations (strict S and boundary H/∂) and coherence laws linking them (`coh-SH`,
`coh-H∂`); additional structure (closure/stability, code/reflection) can be
added as further layers without changing the basic institution-shaped reading.

Assumptions (explicit)
----------------------
- For a textbook institution category story, you may additionally assume/introduce packaged categorical structure on `SigHom` and on the chosen model notion; the core development stays conservative.
- Nontrivial sentence translation is **optional**: the kernel always supports model reduct (`reindexKernel`), while `Sen(σ)` can be added via strict formula translation (`reindexKernelWithFml`) and/or the free boundary sentence layer (`rename∂`).

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: the institution components (signatures, models, sentences, satisfaction condition) as reindexing + satisfaction lemmas.
- Weaker/lax by default: the core stays conservative (no global “category of all signatures/models” is assumed; nontrivial sentence translation is optional).
- Added by ports/adapters: presentation independence and heterogeneous translation live as first-class structure (interlingua + `SatMor`).
- Assumption-scoped: closure/stability (G) and reflection (Code) are extra LogOS structure beyond the bare institution reading, and any completeness/adequacy is explicit.

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `MultiInstitution`):
  `coh-SH` (S↔H), `coh-H∂` (H↔∂).
- In-place model-theory spine:
  `LogOS/Theorems/Meta/CHL/ModelTheory.agda`
  (`For …` → `Profiles`/`AdequacyProfiles`, `LayeredInstitution`,
  `RepresentationIndependence`, `RelativeCompleteness`, `BoundaryLayer`,
  `StrictLayer`, `SeparationBoundary`).
- Representation-independence transport core:
  `LogOS/Theorems/Meta/SemanticsTransport.agda`
  (`translate-id`, `translate-comp-presentations`, `translate-comp`).
- Decode-extensionality discipline (residual-boundary form):
  `LogOS/Theorems/Meta/ConditionalPacks.agda`
  (`DecodeExtensional≈`, `DecodeExtensionalFn≈`).
- Separation/counterexample surface:
  `LogOS/Theorems/Meta/SpectralSeparationOutput.agda`,
  `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda`.
- Signature change (reindexing) surface:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`Reindex`).
- Signature change with strict syntax translation:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`ReindexWithFml`).
- Satisfaction condition as literal precomposition:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`ReindexingSatisfaction`),
  `SatS-precompose`, `SatH-precompose`, `SatHbnd-precompose`.
- Satisfaction condition with strict sentence translation:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`ReindexingSatisfactionWithFml`),
  `SatS-precompose` (now a `↔` over `mapFml`).
- `LogOS.Kernel`-qualified variant:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`ReindexingSatisfactionWithFmlLogic`).
- Sentence/program layer (covariant renaming and functoriality):
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `MultiInstitution.SentenceLayer`):
  `rename∂`, `rename∂-id`, `rename∂-compose`, `interp∂-rename`.
- Strict-syntax interlingua under reindexing:
  `LogOS/Ports/Semantic/InterlinguaStrictReindex.agda` (`translate≈mapFml`, `mapFml-unique`).
- Heterogeneous interlingua (SatMor-level):
  `LogOS/Ports/Semantic/Interoperability.agda` (`heteroCanonicalAdapter`, `heteroAdapter-unique`).
- Strict-to-boundary satisfaction morphism:
  `LogOS/Adapters/Views/SatMor.agda` (`satMor-strict-to-boundary`), with canonical transpilation to ports in
  `LogOS/Ports/Semantic/InterlinguaStrictKernel.agda`.
- Code-to-boundary satisfaction morphism:
  `LogOS/Adapters/Views/SatMor.agda` (`satMor-code-to-boundary`), with canonical transpilation to ports in
  `LogOS/Ports/Semantic/InterlinguaCodeKernel.agda`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- The prose below is explanatory; the statements above are the authoritative claims.

Futamura vs Diagonal (anchored split)
-------------------------------------
Use two explicit claim IDs to keep the story sharp:

- `claim.futamura.transport` (constructive side):
  semantic translation is compositional/unique up to observational equality.
  Anchors:
  `LogOS/Theorems/Meta/CHL/ModelTheory.agda`
  (`For …` → `RepresentationIndependence.SemanticsTransport.translate-comp`,
  `RepresentationIndependence.ForStrictReindex.mapFml-unique`),
  plus canonical adapter uniqueness in
  `LogOS/Ports/Semantic/Interoperability.agda` (`heteroAdapter-unique`).
- `claim.diagonal.limit` (limit side):
  no total self-certifying separation observer (including budgeted variants).
  Anchors:
  `LogOS/Theorems/Meta/CHL/ModelTheory.agda`
  (`For …` → `SeparationBoundary.separation-not-total`,
  `SeparationBoundary.separation-no-self-certification`,
  `SeparationBoundary.separation-diagonal-witness`,
  `SeparationBoundary.budgeted-diagonal-witness`).

Combined reading:
transport/compilation-style semantics works constructively, while diagonalization
forbids universal self-certification. These are complementary, not competing.

Micro-example (the satisfaction condition as a lemma)
-----------------------------------------------------
Fix a signature morphism `σ` and a kernel `K₂`. The surface
`ReindexingSatisfaction σ K₂` packages the satisfaction condition as literal
precomposition:
- `SatS-precompose`, `SatH-precompose`, and `SatHbnd-precompose`.

This is the institution axiom in “proof-relevant” form: not a meta-level
equation, but a named theorem you can transport and compose.

Pointers (no repetition)
------------------------
- Kernel/tier bookkeeping: `docs/LogOS_Core_Spec.lagda.md`.
- Ports/adapters and heterogeneous satisfaction morphisms: `docs/DeepDive/Architecture_PortsAdapters.lagda.md`.
- μ/limit reasoning and hypotheses: `docs/Terminology.lagda.md` and `docs/Kernel/ClaimRegister.lagda.md`.

Extended discussion (optional)
-----------------------------
The remainder recalls standard definitions (institution/multi-institution) and then
spells out the LogOS correspondence in that idiom. The authoritative LogOS claims are
the theorem surfaces cited above.

## Institutions (recall)

We recall the standard definition of an *institution* (Goguen–Burstall) as an abstract
model theory.

**Definition (Institution).** An institution $\mathcal{I}$ is a tuple
$$
  \mathcal{I} = (\mathbf{Sig}, \mathrm{Sen}, \mathrm{Mod}, \models)
$$
consisting of:

- a category $\mathbf{Sig}$ of signatures,
- a functor $\mathrm{Sen} : \mathbf{Sig} \to \mathbf{Set}$ assigning to each signature $\Sigma$
  a set $\mathrm{Sen}(\Sigma)$ of sentences,
- a functor $\mathrm{Mod} : \mathbf{Sig}^{op} \to \mathbf{Cat}$ assigning to each signature $\Sigma$
  a category $\mathrm{Mod}(\Sigma)$ of models,
- for each signature $\Sigma$, a satisfaction relation
  $$
    \models_\Sigma \;\subseteq\; |\mathrm{Mod}(\Sigma)| \times \mathrm{Sen}(\Sigma)
  $$
  between the objects of $\mathrm{Mod}(\Sigma)$ and sentences $\mathrm{Sen}(\Sigma)$,

subject to the **satisfaction condition**: for every signature morphism
$\sigma : \Sigma \to \Sigma'$, every model $M' \in |\mathrm{Mod}(\Sigma')|$, and every sentence
$\varphi \in \mathrm{Sen}(\Sigma)$,
$$
  M' \models_{\Sigma'} \mathrm{Sen}(\sigma)(\varphi)
  \quad\Longleftrightarrow\quad
  \mathrm{Mod}(\sigma)(M') \models_{\Sigma} \varphi.
$$

**Remark (signatures in LogOS).** The Agda implementation is parameterized by a signature
(a record of primitive carriers/operations). The library does provide *structure-preserving*
signature maps (`SigHom` in `LogOS/Base/Signature/Hom.agda`) together with identity and composition,
enough to view signatures as a small category if desired.

Moreover, the kernel interface exposes a concrete semantic reindexing operation along
signature maps:

- `LogOS/Kernel/Reindex.agda` (`reindexKernel`)
- `LogOS/Kernel/Reindex.agda` (`reindexKernelWithFml`, explicit sentence translation)

This is enough to present the *model reduct* part of the institution satisfaction condition
in a way that is aligned with the implemented surface.

Implementation-aligned choice (conservative): default sentence translation can be trivial.
Historically the library only needed the model reduct direction (`Mod`) and so kept `Sen`
constant-on-morphisms. This remains a valid conservative presentation.

However, LogOS now also provides an **optional nontrivial sentence/program layer** that is
functorial along signature morphisms (the institution `Sen` direction):

- `LogOS/Minimal/ConstraintsOverSig.agda` (`Con∂ Sig` and `rename∂ : SigHom Sig₁ Sig₂ → Con∂ Sig₁ → Con∂ Sig₂`)
- `LogOS/Kernel/Reindex.agda` (`reindexKernelWithFml`, for strict formulas)

This makes it possible to state satisfaction conditions with a genuine $\mathrm{Sen}(\sigma)$ map once a model
supplies an interpretation of the atomic generators (e.g. a valuation of interface atoms into
boundary constraints).

For coherence/functoriality across signature morphisms at the kernel-hom level, see:

- `LogOS/Kernel/HomOverSig.agda`

## LogOS kernels as an indexed family of institutions

Fix a LogOS **Kernel** $K$ (in the sense of the Agda record `LogOS.Kernel`). It packages:

- three tiers of truth (S/H/G),
- a boundary constraint language (a preorder),
- and a reflective code interface.

We use the following correspondence to the Agda fields:

- $\mathrm{World} := \texttt{Cosp}$ (worlds/contexts),
- $\mathrm{Con}_\partial :=$ boundary constraints (a preorder),
- $\mathrm{Fml} :=$ strict-layer formulas,
- $\mathrm{Sat}_S(w,\varphi)$ and $\mathrm{Sat}_H(w,c)$ are the S- and H-layer satisfactions,
- $\mathrm{Flow} : \mathrm{Con}_\partial \to \mathrm{Con}_\partial$ is a closure/nucleus
  (this is the `Flow` field of `Truth.GuardedCore.GuardedClosure` in `LogOS/Minimal/Truth.agda`),
- $\mathrm{Th}^\ast$ is a distinguished lax fixed-point witness (interpretation: “global stable truth”),
- $\mathrm{Trans}_H : \mathrm{Fml} \to \mathrm{Con}_\partial$ is the S→H translation.

Disambiguation: this section uses $\mathrm{Con}_\partial$ for **semantic** boundary constraints (the boundary preorder).
Separately, the library also provides an optional **syntactic** boundary sentence layer `Con∂` with renaming `rename∂`
(see `LogOS/Minimal/ConstraintsOverSig.agda`), which can be used as an institution-style `Sen` if desired.

The kernel coherence laws include:
$$
  \mathrm{Sat}_S(w,\varphi) \iff \mathrm{Sat}_H(w,\mathrm{Trans}_H(\varphi))
$$
and the reflective coherence law:
$$
  \mathrm{decode}(\mathrm{Guard}(\gamma)) \;\equiv\; \mathrm{Flow}(\mathrm{decode}(\gamma)).
$$
where $\equiv$ should be read as the library’s propositional equality (Agda’s `_≡_`),
not a judgmental equality.

### S-institution: strict formulas

Define an institution $\mathcal{I}_S(K)$ (“S-tier”) by:

- $\mathbf{Sig}$: the terminal category (we fix the kernel signature in this section),
- $\mathrm{Sen}_S(\Sigma) := \mathrm{Fml}$,
- $\mathrm{Mod}_S(\Sigma) :=$ the discrete category on the set $\mathrm{World}$,
- satisfaction: $w \models_S \varphi$ iff $\mathrm{Sat}_S(w,\varphi)$.

**Remark.** One can strengthen $\mathrm{Mod}_S$ and $\mathrm{Mod}_H$ to preorder categories using a chosen
context relation (`WorldH._≤ctx_`) and rely on monotonicity of satisfaction. When you want the explicit
preorder laws for `_≤ctx_`, supply `CtxPreorder` from `LogOS/Minimal/WorldLaws.agda`. This note keeps
models discrete to stay maximally conservative.

### H-institution: boundary constraints

Define an institution $\mathcal{I}_H(K)$ (“H-tier”) by:

- $\mathrm{Sen}_H(\Sigma) := \mathrm{Con}_\partial$,
- $\mathrm{Mod}_H(\Sigma) :=$ the discrete category on $\mathrm{World}$,
- satisfaction: $w \models_H c$ iff $\mathrm{Sat}_H(w,c)$.

### G-institution: stable theories (Flow pre-fixed points)

The guarded tier is most naturally a **consequence/closure** interface. A standard
model-theoretic presentation uses **pre-fixed points** (stable constraints) of the closure operator as models.

Let $\mathrm{Fix}(\mathrm{Flow})$ be the set of constraints $t \in \mathrm{Con}_\partial$
that are **stable** under the closure, i.e. $\mathrm{Flow}(t) ⊑ t$ (pre‑fixed points).
Because `Flow` is inflationary in LogOS, this automatically implies $t ⊑ \mathrm{Flow}(t)$
as well, hence $t$ is “fixed” up to mutual refinement ($≈$).

Define an institution $\mathcal{I}_G(K)$ (“G-tier”) by:

- $\mathrm{Sen}_G(\Sigma) := \mathrm{Con}_\partial$,
- $\mathrm{Mod}_G(\Sigma) :=$ the preorder of stable constraints $\mathrm{Fix}(\mathrm{Flow})$
  (read as a thin category if you assume proof‑irrelevance for entailment proofs),
- satisfaction: $t \models_G c$ iff $t ⊑ c$ in the boundary preorder.

This is the standard “theories as models” (Lindenbaum-style) move: stable constraints represent theories,
and satisfaction is entailment in the underlying preorder.

In this view, $\mathrm{Th}^\ast$ is a distinguished stable constraint (hence a canonical “model” in $\mathcal{I}_G$).
Interpretation (analogy): “global stable truth”.
Under additional order/continuity structure (not assumed in the minimal kernel interface),
one can upgrade this to a “least pre-fixed point / least model (in the boundary preorder)”
presentation (e.g. via `OmegaCPO` + `FiniteFirst`, and antisymmetry if you want equality-level leastness).

## Multi-institution structure (S/H/G together)

LogOS does not provide only one institution; it provides **three** interlocked tiers.
We therefore present it as a **multi-institution**.

**Definition (Multi-institution, schematic).** A multi-institution consists of:

- a small index category $\mathbf{L}$ of *levels*,
- for each $\ell \in \mathbf{L}$ an institution $\mathcal{I}_\ell$ (over a shared $\mathbf{Sig}$),
- for selected arrows $\ell \to \ell'$ in $\mathbf{L}$, sentence translations
  $\tau_{\ell\to\ell'} : \mathrm{Sen}_\ell(\Sigma) \to \mathrm{Sen}_{\ell'}(\Sigma)$
  that preserve satisfaction in the appropriate direction.

For LogOS, take $\mathbf{L}$ to be the walking diagram
$$
  S \xrightarrow{\;\tau_{S\to H}\;} H \xrightarrow{\;\tau_{H\to G}\;} G
$$
and define:

- $\mathcal{I}_S(K), \mathcal{I}_H(K), \mathcal{I}_G(K)$ as above,
- $\tau_{S\to H} := \mathrm{Trans}_H$ (kernel field),
- the kernel coherence law gives, for each world $w$:
  $$
    w \models_S \varphi \iff w \models_H \tau_{S\to H}(\varphi).
  $$

The map $H \to G$ is not primarily a sentence translation; it is a change of **model class**:
G-models are the $\mathrm{Flow}$-stable constraints, and satisfaction is the underlying
preorder entailment. This is a standard way to express “truth as closure/(pre)fixed point” in a
classical model-theoretic idiom.

## Reflection (Kernel I/O) as internal syntax for G

Beyond the model-theoretic picture, LogOS kernels expose a reflective **code language**:
$$
  \mathrm{encode} : \mathrm{Con}_\partial \to \mathrm{Code},
  \qquad
  \mathrm{decode} : \mathrm{Code} \to \mathrm{Con}_\partial,
  \qquad
  \mathrm{Guard} : \mathrm{Code} \to \mathrm{Code},
$$
with a *pointwise* retraction witness `decode∘encode : ∀ c → decode (encode c) ≡ c`
(no function extensionality is assumed) and the key coherence law:
$$
  \mathrm{decode}(\mathrm{encode}(c)) \;\equiv\; c,
  \qquad
  \mathrm{decode}(\mathrm{Guard}(\gamma)) \;\equiv\; \mathrm{Flow}(\mathrm{decode}(\gamma)).
$$

This can be read as: the G-tier closure operator is **internalised** by a single admissible
code step. This is the interface used by the diagonal/Rice/Tarski-style meta theorems,
while keeping all assumptions explicit.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`
- Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
- Observer semantics (physics-of-information interpretation): `docs/Views/ObserverSemantics.lagda.md`
- Formal semantics contract: `docs/Views/FormalSemantics.lagda.md`

## Reference

- J. A. Goguen and R. M. Burstall, *Institutions: Abstract model theory for specification and programming*, Journal of the ACM, 39(1):95–146, 1992.
