<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Logical Transformers — Design-target spec (code-linked notes)

This document is the design-target, code-linked specification for the v1.1 LT core.
It is mechanically honest: the sync-guard block below imports the modules it tracks, so drift breaks the docs build.

Additional entrypoints:

- overview landing page: `../Orientation/LogOS_Overview.lagda.md`
- repo-aligned implementation specification: `LogOS_Specification.lagda.md`
- mechanisation status + module map: `Implementation_Map.lagda.md`
- explicit strictification surface: `LogOS/API/Strictification.agda`

```agda
{-# OPTIONS --safe #-}
module docs.Core.Spec.LogicalTransformers where

-- Sync guard: modules this doc tracks (core implementations + interface-level valuation layer).
-- If any of these move/rename, `make check-docs` should fail.
import LogOS.Prelude
import LogOS.Syntax.Prop
import LogOS.API.Strictification

-- LT-IMPORTS-BEGIN (generated)
import LogOS.LT.AbstractKZ
import LogOS.LT.AbstractNucleus
import LogOS.LT.Architecture.Apex
import LogOS.LT.Architecture.BiPyramid
import LogOS.LT.Architecture.Definitional
import LogOS.LT.Architecture.Face
import LogOS.LT.Architecture.LogOS
import LogOS.LT.Architecture.Tetrahedron
import LogOS.LT.BoundaryHom
import LogOS.LT.BoundaryImplementation.Core
import LogOS.LT.BoundaryImplementation.Laws
import LogOS.LT.BoundaryImplementation.Strictification
import LogOS.LT.BoundaryImplementation
import LogOS.LT.Coherence
import LogOS.LT.ConPreorder.Antisymmetry
import LogOS.LT.ConPreorder.Discrete
import LogOS.LT.ConPreorder.Indexed
import LogOS.LT.ConPreorder.Isomorphism
import LogOS.LT.ConPreorder.Truth
import LogOS.LT.ConPreorder.Unit
import LogOS.LT.ConPreorder
import LogOS.LT.Contracts.Laws
import LogOS.LT.Contracts
import LogOS.LT.Derivability
import LogOS.LT.Discipline.ArchitectureImplementationLaw.Strictification
import LogOS.LT.Discipline.ArchitectureImplementationLaw
import LogOS.LT.Discipline.AtomicSpine
import LogOS.LT.Discipline.HomDefaults
import LogOS.LT.Discipline.PortStackFolding
import LogOS.LT.Discipline.SuccessorStageFolding
import LogOS.LT.DisplayedThin2Cat.Core
import LogOS.LT.DisplayedThin2Cat.MapDecorated
import LogOS.LT.DisplayedThin2Cat.Product
import LogOS.LT.DisplayedThin2Cat.Strictification
import LogOS.LT.DisplayedThin2Cat.SuccessorStage
import LogOS.LT.DisplayedThin2Cat.Totalisation
import LogOS.LT.DisplayedThin2Cat
import LogOS.LT.Effectivity
import LogOS.LT.Flow
import LogOS.LT.FunPreorder.Pointwise
import LogOS.LT.FunPreorder
import LogOS.LT.Hom.Coercions
import LogOS.LT.Hom.Core
import LogOS.LT.Hom.Laws
import LogOS.LT.Hom.Reasoning
import LogOS.LT.Hom.Strictification
import LogOS.LT.Hom
import LogOS.LT.HomFlow
import LogOS.LT.Index
import LogOS.LT.InstitutionFragment.Strictification
import LogOS.LT.InstitutionFragment
import LogOS.LT.Iteration
import LogOS.LT.Kernel
import LogOS.LT.KernelDefinitional
import LogOS.LT.LOG.ArchitectureBulkBoundary2Cat
import LogOS.LT.LOG.ArchitectureBulkBoundaryContract2Cat
import LogOS.LT.LOG.ArchitectureBulkBoundaryContract2CatDefinitional
import LogOS.LT.LOG.ArchitectureEncode2Cat
import LogOS.LT.LOG.ArchitectureFlowContract2Cat
import LogOS.LT.LOG.ArchitectureFlowContract2CatDefinitional
import LogOS.LT.LOG.ArchitectureQuote2Cat.Displayed
import LogOS.LT.LOG.ArchitectureQuote2Cat
import LogOS.LT.LOG.Boundary2Cat
import LogOS.LT.LOG.BoundaryDecode2Cat
import LogOS.LT.LOG.ClassicalLimit2Cat
import LogOS.LT.LOG.Contract2Cat
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Coverage
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Definitional
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Laws
import LogOS.LT.LOG.Discipline.PortsAsDisplayed
import LogOS.LT.LOG.Discipline.StrictificationAsDisplayed
import LogOS.LT.LOG.EncodePort2Cat.Coherence
import LogOS.LT.LOG.EncodePort2Cat
import LogOS.LT.LOG.Flow2Cat
import LogOS.LT.LOG.GuardedImplementation2Cat
import LogOS.LT.LOG.GuardedImplementationContract2Cat
import LogOS.LT.LOG.GuardedImplementationFlow2Cat
import LogOS.LT.LOG.GuardedKernel2Cat
import LogOS.LT.LOG.Implementation2Cat.Core
import LogOS.LT.LOG.Implementation2Cat.Definitional
import LogOS.LT.LOG.Implementation2Cat.Laws
import LogOS.LT.LOG.Implementation2Cat
import LogOS.LT.LOG.ImplementationContract2Cat.Core
import LogOS.LT.LOG.ImplementationContract2Cat
import LogOS.LT.LOG.ImplementationDecode2Cat.Core
import LogOS.LT.LOG.ImplementationDecode2Cat
import LogOS.LT.LOG.ImplementationFlow2Cat.Core
import LogOS.LT.LOG.ImplementationFlow2Cat
import LogOS.LT.LOG.ImplementationLawStack2Cat
import LogOS.LT.LOG.Kernel2Cat.Core
import LogOS.LT.LOG.Kernel2Cat
import LogOS.LT.LOG.PortReindexing.Strictification
import LogOS.LT.LOG.PortReindexing
import LogOS.LT.LOG.QuotePort2Cat.Coherence
import LogOS.LT.LOG.QuotePort2Cat.Displayed
import LogOS.LT.LOG.QuotePort2Cat.FlowEncodeLayer
import LogOS.LT.LOG.QuotePort2Cat.Port
import LogOS.LT.LOG.QuotePort2Cat
import LogOS.LT.LOG.StrictDecode2Cat
import LogOS.LT.Ports.PortSig
import LogOS.LT.Ports.PortSigStrictification
import LogOS.LT.Ports.PortStack.ClassicalLimit
import LogOS.LT.Ports.PortStack.Coherence
import LogOS.LT.Ports.PortStack.Laws
import LogOS.LT.Ports.PortStack.Raw
import LogOS.LT.Ports.PortStack.RawDefinitional
import LogOS.LT.Ports.PortStack.Unique
import LogOS.LT.Ports.PortStack
import LogOS.LT.Ports.Template.LawSingleton2Cat
import LogOS.LT.Ports.Template.Singleton2Cat
import LogOS.LT.Ports.Template.Singleton2CatDefinitional
import LogOS.LT.Ports.Template.Stack2Cat
import LogOS.LT.Ports.Template.Stack2CatDefinitional
import LogOS.LT.PredicateReindexing
import LogOS.LT.Presentation.ExtensionalMinimality
import LogOS.LT.Presentation.GeneratedImage
import LogOS.LT.Presentation.GeneratedSubobject.Core
import LogOS.LT.Presentation.GeneratedSubobject.Laws
import LogOS.LT.Presentation.Independence
import LogOS.LT.Presentation.Interlingua
import LogOS.LT.Presentation.ObservationInitiality
import LogOS.LT.Presentation.Transport
import LogOS.LT.Presentation
import LogOS.LT.Reflection.Laws
import LogOS.LT.Reflection
import LogOS.LT.Stack.Builders
import LogOS.LT.Stack.Core
import LogOS.LT.Stack.Definitional
import LogOS.LT.Stack.Extend
import LogOS.LT.Stack.Guarded
import LogOS.LT.Stack.Laws
import LogOS.LT.Stack.Program
import LogOS.LT.Stack.Strictification
import LogOS.LT.Stack
import LogOS.LT.Stage.Section
import LogOS.LT.Stage.SuccessorChain
import LogOS.LT.Strictification.Coherence
import LogOS.LT.Sup.AbstractCoKleene
import LogOS.LT.Sup.AbstractGeneratedClosure
import LogOS.LT.Sup.AbstractKleene
import LogOS.LT.Sup.AbstractSigmaDCPO
import LogOS.LT.Sup.FinSup
import LogOS.LT.Sup.SupOmega
import LogOS.LT.Theorems.AbstractCohomology
import LogOS.LT.Theorems.AbstractGaloisConnection
import LogOS.LT.Theorems.ArchitecturalNormalForm
import LogOS.LT.Theorems.ArchitecturalNormalFormStrictification
import LogOS.LT.Theorems.BoundaryGauge
import LogOS.LT.Theorems.Centering
import LogOS.LT.Theorems.CenteringQuote
import LogOS.LT.Theorems.ContextApproximation
import LogOS.LT.Theorems.DependentProbeSuiteRepresentation
import LogOS.LT.Theorems.EffectivePackets
import LogOS.LT.Theorems.Effectivisation
import LogOS.LT.Theorems.EvaluatorReflection
import LogOS.LT.Theorems.ExtensionalReflection
import LogOS.LT.Theorems.PacketCorollaries
import LogOS.LT.Theorems.ProbeSuiteRepresentation
import LogOS.LT.Theorems.QuoteConeMMP.ClosureKernelMMPImpl
import LogOS.LT.Theorems.QuoteConeMMP.IndexedQuotationConeImpl
import LogOS.LT.Theorems.QuoteConeMMP.PreQuotePort
import LogOS.LT.Theorems.QuoteConeMMP.QuotationConeImpl
import LogOS.LT.Theorems.QuoteConeMMP.QuoteStable
import LogOS.LT.Theorems.QuoteConeMMP
import LogOS.LT.Theorems.StableCompletion
import LogOS.LT.Theory.HilbertMP
import LogOS.LT.Theory.Rules
import LogOS.LT.Theory
import LogOS.LT.Thin2Cat.Endo
import LogOS.LT.Thin2Cat.Pointwise.Strictification
import LogOS.LT.Thin2Cat.Pointwise
import LogOS.LT.Thin2Cat.WeakTerminal
import LogOS.LT.Thin2Cat
import LogOS.LT.Thin2Functor.Strictification
import LogOS.LT.Thin2Functor
import LogOS.LT.TypeTheory.Core
import LogOS.LT.TypeTheory.Intensional
import LogOS.LT.TypeTheory.Ports
import LogOS.LT.TypeTheory.Reflection
import LogOS.LT.TypeTheory.Stack
import LogOS.LT.TypeTheory.Strictification
import LogOS.LT.TypeTheory.Surface
import LogOS.LT.TypeTheory
import LogOS.LT.View.Factorisation
import LogOS.LT.View.Family
import LogOS.LT.View.Roles
import LogOS.LT.View.Strictification
import LogOS.LT.View
-- LT-IMPORTS-END

import LogOS.Ports.IO
import LogOS.Ports.Locality.Core
import LogOS.Ports.Causality
import LogOS.Ports.Universality.Budget
import LogOS.Ports.Universality.ArchitectureBudgetBus2Cat
import LogOS.Ports.Universality.BudgetBus2Cat
import LogOS.Ports.Universality.ArchitectureFlowBudget2Cat
import LogOS.Ports.Valuation.QAdapter
import LogOS.Ports.Valuation.ScaleBoundary
import LogOS.Ports.Valuation.AbstractJoinPrequantale
import LogOS.Ports.Valuation.EngineeringDimension
import LogOS.Ports.Valuation.AbstractQuanticNucleus
import LogOS.Ports.Valuation.QAdapterBus
```

Overview
--------

<!-- CLAIM-STAMP: DERIVED | anchor=LogOS/API/LT.agda#LogOS.API.LT -->

This file is the **capstone mathematical specification** for the v1.1 LT core:
definitions, theorem spines, and code anchors into the typechecked Agda development.

Repository-facing status (“what is mechanised now vs planned”) lives in:

- `docs/Core/Spec/Implementation_Map.lagda.md`

Guardrails, build constraints, and “what this does *not* claim” live in:

- `docs/Core/Spec/LogOS_Specification.lagda.md`

Core tooling loops (load-bearing theorems)
-----------------------------------------

These are small theorems that repeatedly collapse “interesting work” into boundary obligations:

- **Normalisation transport (effectivisation):** flow-preserving adapters commute with `Flow ∘ decode` up to refinement.
  - `LogOS/LT/Theorems/Effectivisation.agda` (`normalize-decode-mapCode`)
- **Stable completion (closure-gated self reference):** every kernel canonically factors into stable points, with a
  judgmental-after-unfolding law, hence `≈` by reflexivity: `decode(mapCode γ) ≈ Flow(decode γ)`.
  - “Canonical” here means forced up to observation (pointwise `≈`).
  - `LogOS/LT/Theorems/StableCompletion.agda` (`stableCompletion-law`)
- **Probe suites / locality:** “many local probes” can be bundled as “one distributed view”.
  - uniform representation theorem: `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda` (`ProbeSuiteViewEquiv`, `probeSuiteViewEquiv`)
  - dependent (ultralocal) representation theorem: `LogOS/LT/Theorems/DependentProbeSuiteRepresentation.agda`
    (`DependentProbeSuiteViewEquiv`, `dependentProbeSuiteViewEquiv`)
  - minimality/initiality (observation forces coarsest admissible refinement): `LogOS/LT/Presentation/ObservationInitiality.agda`
    (`SuiteForced`, `SuiteForcedᵈ`)
- **Evaluator reflection:** any evaluator reflects along a closure by precomposition; it is the least stable evaluator above it.
  - `LogOS/LT/Theorems/EvaluatorReflection.agda`
- **Extensional minimality:** `decode` forces the canonical code/morphism refinements (no extra extensionality axioms).
  - `LogOS/LT/Presentation/ExtensionalMinimality.agda`

Coherence modes (refinement < guarded refinement, with strictification quarantined)
----------------------------------------------------------------------------------

- **strict** (`LogOS.API.Strictification.Kernel`): use Agda propositional equality `≡` only in explicit strictification lanes.
- **approx** (`KernelHom`, `KernelHom≈`): use mutual refinement `≈` as the default morphism coherence.
- **under** (`KernelHom⊑`): use one-sided refinement `⊑` for guard-scoped or assumption-scoped transport.

The old H-tier reading survives here: guards are not a separate syntax class, but
boundary constraints made explicit in the morphism/view layer.

Code modules:

- refinement carriers: `LogOS/LT/ConPreorder.agda`
- views + pullbacks: `LogOS/LT/View.agda`

Kernel shape (boundary + code)
------------------------------

A kernel exposes:

- boundary constraints `bnd : ConPreorder`
- code `Code : Set`
- the evaluator `decode : Code → Con bnd`
- optional port `encode : Con bnd → Code` (packaged separately as `EncodePort`)

Crucial: the **code preorder is induced by decoding** (pullback along `decode`).

Code module:

- `LogOS/LT/Kernel.agda`

Morphisms and refinements
-------------------------

A kernel morphism carries:

- `map∂` on boundary constraints (monotone)
- `mapCode` on code
- refinement-first coherence for `decode` (in the core `KernelHom`, via `decode-mapCode : ≈`)
- the primitive split is literal in code: `BoundaryHom` lives in `LogOS/LT/BoundaryHom.agda`, coherence modes live in `LogOS/LT/Coherence.agda`, `BoundaryImplementation` lives in `LogOS/LT/BoundaryImplementation.agda`, and `LogOS/LT/Hom.agda` is the stable façade packaging them together
- `KernelHom⊑ K K' = Σ (BoundaryHom K K') (BoundaryImplementation under)` exposes the guarded/one-sided coherence mode directly
- (architectural split) `KernelHom K K' = Σ (BoundaryHom K K') (BoundaryImplementation approx)` so boundary transport is first-class and the implementation layer is displayed over it
- strict coherence for `decode` only under the explicit `LogOS.API.Strictification` surface (strictification via `Ports.ClassicalLimit`)
- canonical one-sided encode transport law (as the encode-port layer `LogOS.LT.LOG.EncodePort2Cat.WithPort`, via `EncodeLaw`)
- optional stronger mutual encode coherence only through `LogOS.LT.LOG.EncodePort2Cat.Coherence`

Refinement between morphisms is **observational** (pullback refinement along a named boundary readout):
it compares only what is seen in the boundary preorder, not raw code-level structure.

LogOS exposes one canonical and one derived observation view of a kernel morphism `h : KernelHom K K'`:

- **boundary-transport** (`transportView`): `γ ↦ map∂ h (decode γ)`
- **implementation-first** (`obsView`, available through `LogOS.API.Kernel.ImplementationView`): `γ ↦ decode (mapCode h γ)`

The core coherence field `decode-mapCode : ≈` says these two boundary readouts are pointwise `≈`-equivalent.

Accordingly there is one canonical pullback refinement and one derived equivalent presentation between parallel morphisms:

- `f ⇒∂ g` (transport): `∀ γ, map∂ f (decode γ) ≼ map∂ g (decode γ)`
- `f ⇒ g` (implementation-first, derived): `∀ γ, decode (mapCode f γ) ≼ decode (mapCode g γ)`

The bridge lemmas `⇒→⇒∂` and `⇒∂→⇒` show these refinements are logically equivalent (each implies the other). The curated APIs expose `_⇒∂_` flat, keep `_⇒_` behind `ImplementationView`, expose guarded refinement through `LogOS.API.Guarded`, and expose strict equality/coherence only through `LogOS.API.Strictification`.

Code module:

- `LogOS/LT/Hom.agda`

The base thin 2-category `LOG`
------------------------------

`LOG` packages kernels and morphisms as a locally preordered 2-category:

- objects: kernels
- 1-cells: kernel morphisms
- 2-cells: boundary-driven refinements `f ⇒∂ g` (pullback along `transportView`)

Code module:

- `LogOS/LT/LOG/Kernel2Cat.agda`

Architecture, implementation, and law layers
--------------------------------------------

The canonical LT story is now:

1. architecture: `View`, `Kernel`, `BoundaryHom`, `LOGᴳ`
2. implementation: `BoundaryImplementation`, `ImplementationDisplayed`, `LOGᴳʳ`
3. façade: `KernelHom`, `LOG`
4. law: further displayed ports and stacks over the architecture/implementation layer or the preserved façade

Pedantically:

- `LOGᴳ` is the architecture-first thin 2-category of boundary transport;
- `ImplementationDisplayed` is the displayed implementation witness over `LOGᴳ`;
- `LOGᴳʳ` is the Σ-totalisation of that displayed layer;
- `toLOG : LOGᴳʳ → LOG` is the canonical weakening into the stable façade;
- displayed evidence still does not participate in total morphism refinement.

Some preserved doctrine modules are still implemented directly over `LOG` and then reindexed along `toLOG` for the architecture-first basis. That is an implementation choice, not the architectural headline.

Observation-preserving architectural normal form
------------------------------------------------

The LT core now exposes a direct packaged theorem statement:

- `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`

Its content is intentionally positive and code-aligned:

1. observation fixes the canonical pullback refinements;
2. façade morphisms factor through boundary transport plus displayed implementation;
3. displayed Σ-totalisation preserves refinement because displayed evidence is ignored by the hom-preorders;
4. the supported LT layers are recovered as displayed/totalised presentations over the same base;
5. collapse is available only through explicit strictification constructions.

So the public LT façade is recovered from the weaker architecture-first base by
displayed totalisation, while strict collapse enters only through explicit
antisymmetry-indexed extra structure.

Repository-facing inventory note: the detailed member list for this theorem
bundle lives in `docs/Core/Spec/Implementation_Map.lagda.md`.

Fibrewise reflective universality of extensional logic
------------------------------------------------------

The LT core also exposes a relative reflective theorem for explicit
classical-limit fibres:

- `LogOS/LT/Theorems/ExtensionalReflection.agda`

Formally, for every displayed doctrine `D` over `LOG`:

1. the observation-first fibre is
   `ObservationFirstFiber D`;
2. the extensional fibre is
   `ExtensionalFiber D`;
3. the inclusion
   `includeExtensional`
   forgets only the strict decode witness;
4. the reflector
   `strictifyFiber`
   derives that strict decode witness from the explicit antisymmetry payload;
5. for every observation-first object `X` and extensional object `Y`,
   `homwiseExtensionalReflection X Y`
   is a `GaloisConnection` between observation-first morphisms
   `X → includeExtensional Y`
   and extensional morphisms
   `strictifyFiber X → Y`.

Pedantic boundary: this is not a theorem that *all* observation-first logics
freely collapse to extensional ones. The mechanised statement is fibrewise and
relative to explicit classical-limit data already present on the target side.

Self-similarity as presentation
-------------------------------

The refactoring principle is that every port category should *present its own construction*:

1. define a displayed structure over an explicit base thin 2-category;
2. form the Σ-totalisation (Grothendieck-style, refinement inherited from the base; displayed evidence ignored) as the category itself;
3. expose the forgetful functor back to that base;
4. when a port carries an additional law, provide explicit forgetful functors to its
   independent components (so “extra law” is visible as extra data, not as a new layer).

This makes the library self-similar in the strict sense: a port category is the
same categorical pattern as its own explanation.

Mechanisation:

- displayed structure + totalisation: `LogOS/LT/DisplayedThin2Cat.agda`
- one-step successor-stage packaging: `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`
- canonical implementation layer: `LogOS/LT/LOG/Implementation2Cat.agda`
- examples of law layers: `LogOS/LT/LOG/Contract2Cat.agda`, `LogOS/LT/LOG/Flow2Cat.agda`, `LogOS/LT/LOG/EncodePort2Cat.agda`, `LogOS/LT/LOG/ArchitectureBulkBoundary2Cat.agda`
- example of architecture-first port composition: `LogOS/LT/LOG/ArchitectureFlowContract2Cat.agda`, `LogOS/LT/LOG/ArchitectureBulkBoundaryContract2Cat.agda`

Static stacked decorations vs generated hierarchies
---------------------------------------------------

The repo now makes four adjacent moves explicit instead of conflating them:

- **static stacked decorations**: one displayed layer or finite product totalised once (`PortStack`, `Singleton2Cat`, `Stack2Cat`);
- **generated successor stages**: the same one-step totalisation used as a hierarchy constructor (`LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`);
- **generated closures/effectivity**: a guarded closure generated from explicit Kleene data (`LogOS/LT/Sup/AbstractGeneratedClosure.agda`, `LogOS/LT/Effectivity.agda`);
- **stable completion**: the closure-gated semantic factorisation into stable points (`LogOS/LT/Theorems/StableCompletion.agda`).

Pedantic boundary: this is not a generic fixed-point theorem of thin 2-categories. Generated stages, generated closures, and stable completion are distinct constructions with distinct assumptions.

Pedantic port-stack note:
static stacked decorations now also make a naming discipline explicit. Raw
lookup/no-dup/shadowing uses a first-order port label, while the full dependent
payload lives in the packaged port entry. This is why `PortStack` has both a
label-based raw membership lane and an exact typed-entry lane, instead of
treating `Tag : Set ℓ` as the raw symbol.

Numerics as an explicit bus (optional)
-------------------------------------

The design-target spec includes a valuation algebra chunk (scale/time, join/prequantale-like structure).
In 1.1, the kernel core stays small, but numerics can already be made explicit as a port layer:

- `BudgetPort`: a `View` from code into a chosen numeric boundary preorder.
- `BudgetTransport`: an explicit obligation on translations relating source/target budget readouts.
- `LOGᴳʳᵇ`: the default thin 2-category of “kernels with a budget bus” (LOGᴳʳ basis).
- `LOGᵇ`: the observational option (LOG basis), related by a weakening functor.
- `QAdapter` specialises this by deriving the numeric boundary from a chosen **scale** algebra (`ScaleBoundary Q`)
  and defining `LOGQ Q = LOGᵇ (ScaleBoundary Q)`. If you also want to talk about **time**, you make an explicit
  additional choice of clock/presentation `QClock Q` (time monoid + `τ : Time → Scale` + laws).

Beyond the bus base layer, the valuation layer also provides refinement-first algebra and closure tooling:

- finite-join prequantale vocabulary (laws stated in `≈`): `LogOS/Ports/Valuation/AbstractJoinPrequantale.agda`
- finite-join quantic nuclei (join-preserving + lax-multiplicative closures): `LogOS/Ports/Valuation/AbstractQuanticNucleus.agda`
- generated closures by ω-iteration (explicit σ-completeness/continuity assumptions): `LogOS/LT/Sup/AbstractGeneratedClosure.agda`

This keeps refinement between translations observational (2-cells remain pointwise after boundary readout,
with a weakening to base `LOG` via `_⇒∂_`)
while making quantitative assumptions/telemetry first-class and explicitly transported.

The “next move” packaged (institution fragment + KZ-style modality)
-------------------------------------------------------------------

The design-target spec highlights a direct path from the extensional core to a
foundational, functorial, partially reflective “programming language model”:

1. **Make the kernel layer explicitly functorial** (`LOG` as a thin 2-category).  
   Already mechanised: objects `Kernel`, 1-cells `KernelHom`, 2-cells `_⇒∂_` (with implementation-first `_⇒_` available as an equivalent derived view).

2. **Recognise contracts as the Σ-totalisation (category-of-elements-style, refinement inherited from the base; no extra axioms).**  
   `LogOS.LT.LOG.Contract2Cat.WithPort` is the Σ-totalisation for the boundary fiber, with refinement inherited from the underlying kernel morphisms (displayed evidence is proof-irrelevant). If one prefers
   contravariant “substitution”, take opposite fibers `bnd(K)ᵒᵖ` and reindex by `map∂ᵒᵖ`.
   (This is the institution-fragment / predicate-reindexing reading; classical variance is recovered by taking opposites.)

3. **Add the single lax categorical ingredient: Flow-naturality.**  
   For closures `Flow_K` on boundaries, a morphism is flow-preserving when:
   `map∂ (Flow_K c) ≼ Flow_{K'} (map∂ c)`.  
   Mechanised as `KernelHomFlow` and packaged as a thin 2-category of flow-equipped kernels:
   - `LogOS/LT/HomFlow.agda`
   - `LogOS/LT/LOG/Flow2Cat.agda`

4. **Then reflection is a first-class, compositional construct.**  
   `quot ⊣ evalm` reflects into stable points (`Stable`); “out-and-back” yields stabilisation (`Flow`),
   which is the order-theoretic content of partial self reference.

Contracts and foundational logic (boundary as logic)
----------------------------------------------------

The boundary preorder `bnd K` is treated as a *logic of constraints about the kernel*:

- propositions: `Con (bnd K)`
- entailment: refinement `_⊑_ (bnd K)`; on public-facing explanatory surfaces we may also write this as `≼` without changing the semantics
- models: code `Code K`
- satisfaction: `c ≼ decode γ`

Contracts `mkContract K c` are “theories/guards”, and contract morphisms enforce the
satisfaction-preserving inequality `c' ≼ map∂ h c`.

Code modules:

- `LogOS/LT/Contracts.agda`
- `LogOS/LT/LOG/Contract2Cat.agda`

Remark (Σ-totalisation / institution-fragment view)
---------------------------------------------------

This contract construction is the Σ-totalisation (category-of-elements-style, refinement inherited from the base) of the boundary fiber. If you flip
polarity for a textbook contravariant predicate transformer story, use opposite fibers `bnd(K)ᵒᵖ`
and reindex along `map∂ᵒᵖ : bnd(K')ᵒᵖ → bnd(K)ᵒᵖ`. This is the predicate-reindexing / institution-fragment reading:
with covariant model transport it is institution-fragment-like, and the classical institution is recovered by taking opposites.
The corresponding optional view modules are:

- `LogOS/LT/InstitutionFragment.agda`
- `LogOS/LT/PredicateReindexing.agda`

Inputs, outputs, and telemetry (restricted-observation adequacy)
---------------------------------------------------------------

Beyond the canonical boundary evaluator `decode : Code K → Con (bnd K)`, applications often need
**input-indexed outputs** (including telemetry): prompts ↦ responses, traces, logs, counters, etc.

In 1.1 the intended stance is:

- **an output is a view** into a chosen constraint preorder `O : ConPreorder`;
- restricting which inputs are admissible is part of the *boundary interface*;
- adequacy is expressed as order reflection from “cannot be distinguished by admissible I/O”
  back to refinement `≼` (equivalently the underlying `_⊑_` relation).

Mechanised core doctrine:

- `LogOS/Ports/IO.agda`
- port interface: `LogOS/Ports/IO.agda`

Presentation dependence (implementations behind the same boundary)
------------------------------------------------------------------

The kernel fixes a boundary observation interface (`decode`). Many different internal relations can serve as
“implementation structure” (rewrite steps, simulation relations, optimisation relations, ...), as long as they
respect decoded observation.

This is packaged as small “presentation” records that transport any observation-respecting relation into the canonical
refinements:

- `LogOS/LT/Presentation.agda`
- minimal derivability layer (provability from a base assumption): `LogOS/LT/Derivability.agda`
- upgraded “initiality” layer (observation forces the coarsest admissible refinement):
  `LogOS/LT/Presentation/ObservationInitiality.agda` (`SuiteForced`, `SuiteForcedᵈ`,
  `suitePresentation`, `suitePresentationᵈ`, `suiteDerivationSystem`,
  `suiteDerivationSystemᵈ`, and their canonical suite wrappers)
- representation theorem (probe suite ↔ distributed view): `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`
  (round-trip laws are pointwise on observations; no extensionality principle needed)
- transport of proof systems along meaning-preserving translations: `LogOS/LT/Presentation/Interlingua.agda`
<!-- CLAIM-STAMP: DERIVED | anchor=LogOS/LT/Presentation/Independence.agda#presentationsAgree -->
- presentation independence for complete presentations over one fixed view/suite:
  `LogOS/LT/Presentation/Independence.agda`

In particular, `LogOS/LT/Derivability.agda` provides `Deriv` as the reflexive-transitive closure of a primitive
rule relation and the corresponding `derivPresentation` constructor. Together
with the suite constructors and the transport/independence modules above, this
completes the v1.1 observation/evaluation lane.

Extensional minimality (decode forces refinement)
------------------------------------------------

Once `decode` is treated as the observation boundary, several obligations become *derived*.
See:

- `LogOS/LT/Presentation/ExtensionalMinimality.agda`

This includes:

- `CodeRefineForced`: any relation that makes `decode` monotone is contained in the induced code preorder.
- `mapCode-mono`: monotonicity of code transport is derived from boundary monotonicity + decode coherence.
- `MorRefineForced∂`: any relation on morphisms that respects transported boundary observation is contained in the canonical refinement `_⇒∂_`.
- `MorRefineForced`: the implementation-first formulation is retained as an equivalent derived corollary via `⇒∂→⇒`.
- `whiskerL` / `whiskerR`: refinement is preserved under composition (whiskering is monotone).

Iteration (boundary reduction)
------------------------------

Spec v5.8 makes explicit a computational reading: code evolution is a chosen presentation of boundary dynamics.

Mechanised lemma:

- `decode-iter-mapCode⊑` / `decode-iter-mapCode⊒`: for an endomorphism `f : KernelHom K K`,
  directional boundary refinements (local refinement).
- `decode-iter-mapCode`: derived mutual refinement (observational equivalence),
  `decode (iter (mapCode f) n γ) ≈ iter (map∂ f) n (decode γ)`.
- optional `run`: if the boundary has finite joins (`FinSup`), σ-directed ω-suprema (`SigmaDCPO`),
  and a closure (`GuardedClosure`), define `run` as the derived ω-supremum (`supω`) of the
  normalised trace.

Code module:

- `LogOS/LT/Iteration.agda`

Flow and reflection (partial self reference)
--------------------------------------------

Flow is a guarded closure on boundary constraints, and stable points package stability witnesses.
Reflection is induced by the closure:

- `quot : bnd → Stable Flow`
- `evalm : Stable Flow → bnd`

with `quot ⊣ evalm` as a preorder adjunction; “out-and-back” yields stabilisation (`Flow`), not identity.

Code modules:

- `LogOS/LT/Flow.agda`
- `LogOS/LT/Reflection.agda`
- `LogOS/LT/AbstractKZ.agda`

A canonical “stable completion” factorisation (tooling loop) is available:

- `LogOS/LT/Theorems/StableCompletion.agda` (`stableCompletion`, `stableCompletion-law`).

The quotation story is now deliberately one theorem family:

- `StableCompletion` gives the canonical completion into stable points.
- `CenteringQuote` re-exports the no-fork and factorisation consequences for
  quotation surfaces.
- `BoundaryAsCode` gives the dependent boundary-as-code analogue: transparent
  denotations are forced to agree with the canonical denotation up to boundary
  transport and observational equivalence, and the normalised transparent code
  semantics classifies exactly the same code preorder as the source locality
  kernel.

Flow-preserving morphisms
-------------------------

To make closure functorial across translations, the spec isolates a single contract law inequality:

- `KernelHomFlow`: `map∂ (Flow c) ≼ Flow (map∂ c)`

This is the “lax naturality” of the modality; it supports the flow-preserving thin 2-category `LogOS.LT.LOG.Flow2Cat.WithPort`.

Code modules:

- `LogOS/LT/HomFlow.agda`
- `LogOS/LT/LOG/Flow2Cat.agda`

Reflection of evaluators along closure (universal property)
---------------------------------------------------------

Given a guarded closure `N : Y → Y` on any preorder `Y` (monotone + inflationary + lax-idempotent),
any monotone evaluator `T : Y → O`
reflects to an `N`-stable evaluator by precomposition:

- `T^N ≡ T ∘ N`

Mechanised universal property (spec section “Reflection of evaluators along closure”):

- `T ≼ T^N` (inflation)
- `T^N ∘ N ≈ T^N` (N-stability)
- for any `N`-stable `S` with `T ≼ S`, we have `T^N ≼ S` (least N-stable extension)

Code module:

- `LogOS/LT/Theorems/EvaluatorReflection.agda`

For adjunction-induced closures, the same story is exposed as a reflective-image
theorem:

- every right-image point is stable for the induced closure, and
- every stable point is represented by the right image up to refinement witness.

Code module:

- `LogOS/LT/Theorems/AbstractGaloisConnection.agda`

Next work items (spec → code)
-----------------------------

1. Start the **hexagonal boundary** for applications: ports (especially opacity/observation) + small packs/demos.
2. Keep this as an explicit optional doctrine module and use it to decorate
   transformer stacks that need bulk-level resource accounting.
3. Defer the quantitative adapter + finite-join prequantale layer until a pack needs explicit grades/cost/time.
