<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS LT — Implementation map (v1.1)

This file is **repository-facing**: it records what is mechanised (and where), and what is still only present in
the design-target spec narrative.

Capstones:

- Pure mathematical spec: `docs/Core/Spec/LogicalTransformers.lagda.md`
- Repo-aligned specification + guardrails: `docs/Core/Spec/LogOS_Specification.lagda.md`

```agda
{-# OPTIONS --safe #-}
module docs.Core.Spec.Implementation_Map where

import LogOS.API.LT
import LogOS.API.Theorems.Core
```

Spine summary (what everything reduces to)
-----------------------------------------

All implemented pieces factor through the same path:

- `ConPreorder` → `View` → `Kernel` → `KernelHom`
- `LOG` as the thin 2-category of kernels
- ports as displayed structure (`DisplayedThin2Cat`)
- totalisations as decorated categories (`DecoratedThin2Cat`)
- successor stages as named one-step totalisations (`SuccessorStage`)
- independent composition via `ProductDisplayed`
- law-ports with explicit forgetful projections

Tetrahedron map (equator / construction / discipline / realisation / faces)
---------------------------------------------------------------------------

The same construction spine has a particularly clean repository reading:

- **equator (preserved observational comparison):**
  `LogOS.API.Architecture.Equator` (re-exported by `LogOS.API.LT`; exports `LOG`).
- **discipline apex (displayed growth):**
  `LogOS.API.Architecture.Discipline` (exports `LOGᴳ`, `LOGᴳʳ`, `toLOG`,
  `DisplayedThin2Cat`, and the port stack authoring templates).
- **construction apex (presentation growth):**
  `LogOS.API.Architecture.Construction` (exports stacks/programs and
  `stackKernel` / `programKernel`).
- **realisation apex (shared-boundary many-realisations):**
  `LogOS.API.Architecture.Realisation` (exports `DependentLocalSemantics`,
  `RealisationFamily`, the realisation apex, and the canonical denotation
  surface into boundary-as-code).
- **faces (derived two-apex views over the same equator):**
  `LogOS.API.Architecture.Faces` (exports `bipyramidFace`,
  `hexagonalFace`, `sharedBoundaryFace`, the canonical realisation-specialised
  face constructors, and the refinement-safe projection `kernelOfToLOG`), while
  `LogOS.API.Strictification.Architecture.Faces` carries the explicit strict
  reindexing/weakening helpers from `LogOS.LT.LOG.PortReindexing.Strictification`.

The packaging itself (no new semantics) is on the default curated LT surface:

- `LogOS.API.LT` (which re-exports `LogOS.API.Architecture`)

Capstone packaged theorem
-------------------------

The current capstone theorem surfaces are split by design:

- `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`
- `LogOS/LT/Theorems/ArchitecturalNormalFormStrictification.agda`
- `LogOS/LT/Theorems/ExtensionalReflection.agda`

This is the detailed theorem-inventory page for those bundles. The other spec
notes only summarize them and point here.

The refinement bundle packages the main LT storyline into one theorem bundle
`ObservationPreservingArchitecturalNormalForm` with witness
`architecturalNormalForm`. Concretely, the bundle exposes:

- observation-forced canonical refinements (`presentation↔canonical`,
  `SuiteForced`, `SuiteForcedᵈ`, `CodeRefineForced`, `MorRefineForced∂`,
  `MorRefineForced`);
- façade factorisation through boundary transport plus displayed
  implementation (`kernelHomFactorises`, `implementationTotalisation`);
- invariance of total refinement/equivalence under Σ-totalisation
  (`total⊑→base⊑`, `base⊑→total⊑`, `total≈→base≈`, `base≈→total≈`);
- definitional displayed/totalised presentations of the supported canonical LT
  layers (`supportedArchitectureLayers`).

The strictification addendum lives separately in
`ArchitecturalNormalFormStrictification`, which is the only theorem bundle that
exports the equality witnesses `toFacadeHom-fromFacadeHom≡id`,
`fromFacadeHom-toFacadeHom≡id`, the strictification-layer support witnesses,
and the typed strictification operators `strictifyDisplayed` / `strictifyStack`.

Repository reading: the theorem is not a new semantic layer. It is the
packaged statement that the repo’s existing architecture/implementation/law
discipline already proves.

The second theorem surface is deliberately relative: `ExtensionalReflection`
does not claim a global free collapse of all observation-first logic. Instead it
packages the fibrewise statement that, for every displayed doctrine `D` over
`LOG`, the classical-limit-equipped observation-first fibre reflects into its
strict/extensional subfibre by `strictifyFiber`, with homwise universal
property `homwiseExtensionalReflection`.

The broadest Apps-side metatheorem now packages those LT results together with
the LogicArchitecture shadow theorem:

- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`

Its main repository-level object is `MechanisableLogicWorld`, with
`MechanisableBoundarySemanticsTheorem` and
`mechanisableBoundarySemanticsTheorem` retained as stable theorem-facing
aliases. This is the main repository-level theorem package about the logic: a
foundational refinement logic of mechanisable boundary semantics, where each
reflected hom is canonically an LT kernel, complete presentations
over one fixed boundary world are equivalent interfaces to that kernel’s
canonical preorder, guarded self-reference is internal there via
`BoundarySelfReferenceFibre`, and extensionality appears only as explicit
reflective collapse.

The new apps-side summit capstone sits one layer above that seed theorem
package:

- `LogOS/Apps/Summit/Policy.agda`
- `LogOS/Apps/Summit/Recognition.agda`
- `LogOS/Apps/Summit/Quantitative.agda`
- `LogOS/Apps/Summit/Obstruction.agda`

Pedantic boundary: this is not a second capstone theorem world. It is an
apps-side capstone surface that packages recognition by conservative generalisation,
collected quantitative consequences, and the guarded obstruction over a chosen
recognised fragment.

Implemented now (high-level)
----------------------------

This list is descriptive. For authoritative definitions and theorem spines, use:
`docs/Core/Spec/LogicalTransformers.lagda.md`.

- S/G discipline via `≡` vs `⊑` (mutual refinement `≈` derived)
- view/pullback discipline for presentation-induced relations
- kernels: boundary preorder + code + `decode` (optional `encode` port)
- kernel morphisms: boundary/code action + refinement-first coherence (`≈`), with equality quarantined to explicit `Strictification` lanes (`LogOS.API.Strictification.Kernel` / `Ports.ClassicalLimit`)
- 2-cells/refinement of morphisms as observational pullbacks on boundary readouts (base `LOG` uses boundary-driven `_⇒∂_` / `transportView`; implementation-first `_⇒_` / `obsView` remains available only as an equivalent derived view)
- thin 2-category packaging (`LOG`)
- displayed/Σ-totalisation (Grothendieck-style; refinement inherited from base, displayed evidence ignored) factoring for “decorated kernels” (`DisplayedThin2Cat`)
- successor-stage packaging for reusable one-step displayed-totalisation constructors (`LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`)
- port composition by products of displayed layers (`ProductDisplayed`)
- flow/guarded closure + stable points (`Stable`) + reflection (`quot ⊣ evalm`)
- flow-preserving morphisms (`LogOS.LT.LOG.Flow2Cat.WithPort`) and encode-equipped kernels (`LogOS.LT.LOG.EncodePort2Cat.WithPort`)
- optional completeness layer: finite joins (`FinSup`) + σ-directed ω-suprema (`SigmaDCPO`), derived `supω`, and μ/ν fixed point spines (`Kleene`, `CoKleene`)
- generated guarded closures/effectivity from explicit Kleene data (`LogOS/LT/Sup/AbstractGeneratedClosure.agda`, `LogOS/LT/Effectivity.agda`)
- contracts + satisfaction (`LogOS.LT.LOG.Contract2Cat.WithPort`) and institution-fragment / predicate-reindexing packaging
- dependent locality port (probe-suite packaging; canonical “ultralocal” locality via `LocalBoundary I O = DFunPreorder I O`)
  with a uniform constant-family wrapper (`LocalityPort`)
- generic “one shared boundary, many realisations” pattern factored out as
  `LogOS/Ports/Realisations/DependentStack.agda` (downstream packs specialise
  this surface without changing the LT core)
- restricted products / “almost everywhere” laws as an explicit, compositional layer (`RestrictedProduct`)
- local reversibility vocabulary (`OrderIso`) and Deutsch-style category packaging over a fixed shared distributed-semantics ledger
  (parameterised by `DependentLocalSemantics`; code: `LogOS.Ports.AbstractDeutsch2Cat.Deutsch2CatLocal.Locality.WithPort` and
   `LogOS.Ports.AbstractDeutsch2Cat.Deutsch2CatLocal.Deutsch.WithPort`; uniform recovered as a constant-family special case)
- explicit cost/Landauer assumptions as an optional, refinement-first theorem layer:
  `LogOS/Ports/AbstractLandauer/Ledger.agda` and the corresponding law-port totalisation `LogOS/Ports/AbstractLandauer2Cat.agda`
- general causal physical slice plus default thermodynamic extension:
  `LogOS/Ports/AbstractCausal2Cat.agda`,
  `LogOS/Ports/AbstractCausalLandauer2Cat.agda`
- narrower reversible bookkeeping slice when the arrow already lies in `LOGᴰ`:
  `LogOS/Ports/AbstractCausalLandauer2Cat.agda`
- tiny LT factorisation seam plus an optional opacity pack with a downstream
  Landauer bridge:
  `LogOS/LT/View/Factorisation.agda`,
  `LogOS/Ports/Opacity/Distinguishability.agda`,
  `LogOS/Ports/Opacity/Obstruction.agda`,
  `LogOS/Ports/Opacity/Profile.agda`,
  `LogOS/Ports/Opacity/FiniteCompression.agda`,
  `LogOS/Ports/AbstractLandauerObservational.agda`
- guarded Lawvere theorem pack and ZFC predicate-reification specialization:
  `LogOS/Ports/Reification/GuardedLawvere.agda`,
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/GuardedLawvere.agda`
- optional “prequantum” (CQM-style) structure layers over a chosen thin 2-category:
  symmetric monoidal structure + discard + purification (packs), and their displayed/Σ-totalised law-port variants
  (`LogOS/Ports/PreQuantum/*.agda`, plus `LogOS/Ports/PreQuantum/*2Cat.agda`)
- probe-suite representation theorem (many local probes ↔ one distributed view): `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`
- observation-preserving architectural normal form bundle:
  `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`
- kernel-native derivability layer (minimal presentation layer via presentations)
- stacks (“a stack of transformers is a transformer”) and a small macro language of views
- effectivisation tooling loop (normalisation transport) + effective packets corollaries
- canonical denotation into boundary-as-code + guarded self-reference (`QuotePort`) + stable completion into stable points:
  `LogOS/LT/Theorems/StableCompletion.agda`
- meta-theory pack (Apps; explanatory, not required by the LT core):
  thin shadow factorisation + boundary-controlled approximation
  (`LogOS/Apps/LogicArchitecture/MetaTheory/Basis.agda`,
   `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`,
   `docs/Core/MetaTheory/Basis.lagda.md`,
   `docs/Core/MetaTheory/Observation_Controlled_Approximation.lagda.md`)

Static decorations vs generated ladders
---------------------------------------

LogOS now separates four closely related but non-identical moves:

- **static stacked decorations**: choose a displayed layer once and totalise once (`PortStack`, `Singleton2Cat`, `Stack2Cat`);
- **generated successor stages**: reuse the same one-step totalisation as a hierarchy constructor (`SuccessorStage`);
- **generated closures/effectivity**: build a guarded closure from explicit Kleene data (`AbstractGeneratedClosure`, `Effectivity`);
- **stable completion**: factor a kernel into stable points after choosing a closure (`StableCompletion`).

Pedantic boundary: this is not a generic fixed-point theorem about thin 2-categories. Stage generation, generated closure, and stable completion are different layers with different assumptions.

Mechanisation status (storyline map)
------------------------------------

This table is the single authoritative mapping of spec storylines to the current v1.1 mechanisation.

| Spec storyline | Agda modules (1.1) | Status |
|---|---|---|
| Notation and S/G/H discipline | `LogOS/LT/ConPreorder.agda`, `LogOS/Syntax/Prop.agda` | Implemented |
| Valuation algebra (finite-join prequantale adapters) | `LogOS/Ports/Valuation/QAdapter.agda`, `LogOS/Ports/Valuation/ScaleBoundary.agda`, `LogOS/Ports/Valuation/AbstractJoinPrequantale.agda`, `LogOS/Ports/Valuation/AbstractQuanticNucleus.agda`, `LogOS/LT/Sup/AbstractGeneratedClosure.agda`, `LogOS/API/Valuation.agda` | Implemented (generic generated-closure core lives in LT and is surfaced directly through the valuation API) |
| Landauer-style cost assumptions | `LogOS/Ports/AbstractLandauer/Ledger.agda`, `LogOS/Ports/AbstractLandauer2Cat.agda` | Implemented (assumption pack + law-port totalisation; not a kernel axiom) |
| General causal physical slice | `LogOS/Ports/AbstractCausal2Cat.agda` | Implemented (causality as a law-port over the unrestricted physical kernel category induced by a shared distributed-semantics ledger) |
| Irreversibility-facing thermodynamic layer | `LogOS/Ports/AbstractCausalLandauer2Cat.agda` | Implemented (Landauer law-port stacked over the general causal slice; the reversible Deutsch fragment is handled as a restriction of the same ambient causal story) |
| Opacity factorisation / finite distinguishability loss | `LogOS/LT/View/Factorisation.agda`, `LogOS/Ports/Opacity/Port.agda`, `LogOS/Ports/Opacity/Factorisation.agda`, `LogOS/Ports/Opacity/Distinguishability.agda`, `LogOS/Ports/Opacity/Obstruction.agda`, `LogOS/Ports/Opacity/Profile.agda`, `LogOS/Ports/Opacity/FiniteCompression.agda`, `LogOS/API/Opacity.agda`, `LogOS/Ports/AbstractLandauerObservational.agda`, `LogOS/Apps/Irreversibility/BitResetCompression.agda`, `LogOS/Apps/Irreversibility/BitResetLandauer.agda`, `LogOS/Apps/Irreversibility/MeasurementCoarseGrainCompression.agda`, `LogOS/Apps/Opacity/TagOpacity.agda` | Implemented (optional opacity pack over a minimal LT seam; finite count-loss is derived, not primitive) |
| Guarded Lawvere / diagonal obstruction | `LogOS/Ports/Reification/GuardedLawvere.agda`, `LogOS/API/Reification.agda`, `LogOS/Apps/ZFC/Stack/AsymptoticReification/GuardedLawvere.agda` | Implemented (guarded/refinement-first schema; concrete ZFC specialization requires explicit `FlowCollapse`) |
| Prequantum (CQM-style) extra structure (monoidal/discard/purification) | `LogOS/Ports/PreQuantum/Monoidal.agda`, `LogOS/Ports/PreQuantum/Discard.agda`, `LogOS/Ports/PreQuantum/Purification.agda`, `LogOS/Ports/PreQuantum/Discard2Cat.agda`, `LogOS/Ports/PreQuantum/Purification2Cat.agda`, `LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda` | Implemented (packs + displayed/Σ-totalised law ports; the public entrypoint now states directly that purification stacks over the causal + Landauer base and uses explicit witness composition data) |
| Base thin 2-category `LOG` | `LogOS/LT/LOG/Kernel2Cat.agda`, `LogOS/LT/Thin2Cat.agda` | Implemented |
| Observation-preserving architectural normal form | `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`, `LogOS/LT/Discipline/ArchitectureImplementationLaw.agda`, `LogOS/LT/LOG/Discipline/PortsAsDisplayed.agda`, `LogOS/LT/LOG/Discipline/StrictificationAsDisplayed.agda`, `LogOS/Checks/ArchitecturalNormalForm.agda` | Implemented |
| Fibrewise reflective strictification of extensional logic | `LogOS/LT/Theorems/ExtensionalReflection.agda`, `LogOS/LT/LOG/ClassicalLimit2Cat.agda`, `LogOS/LT/LOG/StrictDecode2Cat.agda`, `LogOS/Checks/ExtensionalReflection.agda` | Implemented |
| Capstone theorem: mechanisable boundary semantics (Apps-side composite metatheorem) | `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`, `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/ObservationReflection/Core.agda`, `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`, `LogOS/LT/Theorems/ExtensionalReflection.agda`, `LogOS/Checks/FoundationalLogic.agda` | Implemented |
| Summit capstone: recognition, strong downstream mechanisability, and obstruction over mechanisable fragments | `LogOS/Apps/Summit/Policy.agda`, `LogOS/Apps/Summit/Recognition.agda`, `LogOS/Apps/Summit/Quantitative.agda`, `LogOS/Apps/Summit/Obstruction.agda`, `LogOS/Apps/Summit/Theorem.agda`, `LogOS/Checks/Summit.agda` | Implemented |
| Kernel shape (boundary + code + decode) | `LogOS/LT/Kernel.agda`, `LogOS/LT/View.agda` | Implemented |
| Kernel morphisms (decode coherence) | `LogOS/LT/Hom.agda` | Implemented |
| 2-cells (canonical boundary-driven refinement `_⇒∂_`, implementation-first `_⇒_` equivalent) | `LogOS/LT/Hom.agda`, `LogOS/LT/LOG/Kernel2Cat.agda` | Implemented |
| Contracts and satisfaction | `LogOS/LT/Contracts.agda`, `LogOS/LT/LOG/Contract2Cat.agda` | Implemented |
| Observations and evaluation | `LogOS/LT/Presentation.agda`, `LogOS/LT/Derivability.agda`, `LogOS/LT/Presentation/ObservationInitiality.agda`, `LogOS/LT/Presentation/Transport.agda`, `LogOS/LT/Presentation/Interlingua.agda`, `LogOS/LT/Presentation/Independence.agda` | Implemented |
| Extensional minimality | `LogOS/LT/Presentation/ExtensionalMinimality.agda` | Implemented |
| Normalisation doctrine (guarded closure) | `LogOS/LT/Flow.agda`, `LogOS/LT/LOG/Flow2Cat.agda` | Implemented |
| Reflection along closure | `LogOS/LT/Reflection.agda`, `LogOS/LT/Theorems/EvaluatorReflection.agda` | Implemented |
| Partial self-reference via fixed points | `LogOS/LT/Reflection.agda`, `LogOS/LT/Sup/AbstractKleene.agda`, `LogOS/LT/Sup/AbstractCoKleene.agda` | Implemented (σ/ω interfaces) |
| Bulk–boundary adjunctions (economy layer, optional) | `LogOS/LT/LOG/ArchitectureBulkBoundary2Cat.agda`, `LogOS/LT/LOG/ArchitectureBulkBoundaryContract2Cat.agda` | Implemented |
| KZ-style modalities (guarded closure + reflection) | `LogOS/LT/Flow.agda`, `LogOS/LT/Reflection.agda`, `LogOS/LT/AbstractKZ.agda` | Implemented |
| Locale-style nuclei (meet preservation, optional) | `LogOS/LT/AbstractNucleus.agda` | Implemented (optional upgrade) |
| “Guard modality commutes with decoding” lemmas | `LogOS/LT/Iteration.agda` | Implemented |

Further planned work (beyond the storylines above)
--------------------------------------------------

- richer I/O and telemetry doctrines (more ports, more adapters)
