<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Foundational Definition (Reference Spec)

```agda
{-# OPTIONS --safe #-}
module docs.Definition_Spec where

-- Sync guard: these imports are the implemented modules this spec summarizes.
-- If a referenced module is renamed/removed, the docs build fails.
import LogOS.Prelude
import LogOS.Base.Signature
import LogOS.Minimal.Adapter
import LogOS.Minimal.World
import LogOS.Minimal.Con
import LogOS.Minimal.Adjunction
import LogOS.Minimal.Truth
import LogOS.Kernel
import LogOS.Kernel.Endo
import LogOS.Kernel.TensorEndo
import LogOS.Kernel.TensorDSL
import LogOS.Kernel.Graded
import LogOS.Kernel.Graded.Endo
import LogOS.Kernel.Graded.Hom
import LogOS.Kernel.Graded.All
import LogOS.Theorems.Boundary.Graded.All
import LogOS.Kernel.Boundary
import LogOS.Boundary.IO
import LogOS.Boundary.Semantics
import LogOS.Free.Constraints
import LogOS.Free.ConstraintsIndexed
import LogOS.Free.ConstraintsOverSig
import LogOS.Free.All
import LogOS.Kernel.Initial
import LogOS.Kernel.Infinite.Initial
import LogOS.Theorems.Projective
import LogOS.Theorems.Reflection.QuanticNucleus
import LogOS.Theorems.Reflection.NucleusMu
import LogOS.Theorems.Reflection.ForcingSheaves
import LogOS.Theorems.Meta.Assumptions
```

For a newcomer-friendly architecture overview, see `docs/Definition.lagda.md`.

Overview
--------
This file is a compact, code‑accurate summary of the LogOS core. All axioms are
explicit record fields; continuity/fixpoint properties are model‑local assumptions.
Hook: one kernel, many semantics — packs and views add structure without changing the core.

Conventions and Notation
------------------------
- Levels: records are level‑polymorphic; higher universes appear only when fields range over `Set`.
- Equality: propositional `_≡_` only; decode‑equality is `_≃K_` from `LogOS/Syntax/Eq.agda` (module `ForKernel`).
- Orders: preorders by default; antisymmetry is optional (`PartialOrder` in `LogOS/Minimal/Con.agda`).
- Coherence: use `_↔_` (pairs of maps), not definitional equality.
- Bottom/negation: `⊥` and `¬_` from `LogOS.Syntax.Prop`.

Universe/Prelude
----------------
- Canonical import: `open import LogOS.Prelude` (levels, `_≡_`, and small shims), plus `Topℓ : Set ℓ`.

Signature
---------
Primitive carriers and operations live in `LogOS.Base.Signature`:
- `Sorts` (`Iface`, `Cosp`, `∂Cosp`)
- `CospanOps` (`src`, `tgt`, `idC`, `_∘C_`, `_⊕C_`, `_⊗C_`)
- `BoundaryOps` (`src∂`, `tgt∂`, `id∂`, `_∘∂_`, `_⊕∂_`, `_⊗∂_`, `from∂`, `to∂`)
`LogOSSignature` bundles these as `sorts`, `cospanOps`, `boundaryOps`.

```agda
-- Anchor: the signature exports *program-level* boundary maps `to∂/from∂`.
open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)

to∂-sig
  : ∀ {ℓ} (Sig : LogOSSignature ℓ)
  → LogOSSignature.Cosp Sig → LogOSSignature.∂Cosp Sig
to∂-sig Sig = LogOSSignature.to∂ Sig

from∂-sig
  : ∀ {ℓ} (Sig : LogOSSignature ℓ)
  → LogOSSignature.∂Cosp Sig → LogOSSignature.Cosp Sig
from∂-sig Sig = LogOSSignature.from∂ Sig
```

Adapter and Worlds (S/H/G)
--------------------------
`QAdapter` packages a finite‑join unital quantale plus a time monoid homomorphism `τ : Time → Scale`;
ω‑sup / infinite-join completeness is *not* assumed on `Scale` (ω‑sup interfaces live separately via
`OmegaCPO`/`FiniteFirst`).
Worlds (`LogOS.Minimal.World`) are tiered: `WorldS = Cosp`, `WorldH Q` adds context flow, and
`WorldG Q = WorldH Q`.

`LogOS.Minimal.Con` defines:
- `ConPoset`: `Con`, `_⊑_`, `refl`, `trans`
- `BulkBoundary`: `bulk`, `bnd`
`LogOS.Minimal.Adjunction` defines:
- `MonoidalPoset`: `_⊗_`, `I`, `mono⊗`
- `LaxAdjunction`: `ext`, `bnd`, `unit-lax`, `counit-lax`
- `LaxMonoidalAdjunction`: `core`, `ext-⊗-lax`, `ext-I-lax`, `bnd-⊗-lax`, `bnd-I-lax`

Truth Interfaces (S/H/G)
------------------------
`LogOS.Minimal.Truth` packages S/H/G layers:
- `StrictTruth.StrictLayer` (`Sat_S`)
- `HomotypicalTruth.HLayer` (`Sat_H`, monotonicity) + `HomotypicalTruth.Invariance` (`Inv_H`, `infl`, `idemp-lax`)
- `GuardedTruth.GuardedClosure` (`Flow`, `mono`, `infl`, `idemp-lax`, `Th*`, `Th*-fixed`)
- Optional graded closure (`GuardedCore.GradedClosure`) and ω‑sup structure (`OmegaCPO`, `FiniteFirst`)
`Th*` lives in preorder form. When ω‑sup structure is provided, `FiniteFirst`
exposes an ω‑supremum presentation (`Th⋆-as-sup`) of the same fixed‑point story.
Note: some endomap DSL modules use the conventional name `Th⋆K` for the
distinguished witness `Th*` (not an ω‑supremum); see `LogOS/Kernel/LogicKernel/Endo.agda`.

Kernel (Integrated Model)
-------------------------
`LogOS.Kernel` integrates S/H/G truth and reflection. Key groups:
- Worlds/constraints: `HWorld`, `BB`, `MBulk`, `MBnd`, `Holo`.
- H‑tier truth/invariance: `HTruth`, `HInv`.
- Boundary + S/H coherence: `Sat_H_bnd`, `sat-coh`, `Fml`, `Strict`, `TransH`, `coh-LH`.
- Boundary monotonicity (derived): `Sat_H_bnd-mono`, `Sat_H_bnd-mono-ctx` (via `sat-coh` + HTruth).
- G‑tier closure: `GTruth` with `Flow` and `Th*` (`Th*-fixed`).
- Code/reflection: `Code`, `encode/decode`, `Guard/Body`, `FlowCode`, `guard-decode`,
  `γ*`/`decode-γ*`, `reify`, `Body∂` and `body-decode`.
- R‑tier monotonicity (derived): `Sat_R-mono`, `Sat_R-mono-ctx` in `LogOS/Kernel/LogicKernel/Tiers.agda`.

Reflection (Cross‑Cutting Structure)
------------------------------------
Reflection is an axis across S/H/G and the bulk↔boundary interface:
- Shared shape: `Projector` + fixed points (`LogOS/Theorems/Reflection/Projector.agda`).
- S/presentation: `reify` is decode‑inert (`LogOS/Theorems/Boundary/Reflection.agda`).
- G/closure: `Flow` is a projector‑shape closure (`LogOS/Minimal/Truth.agda`).
- H/invariance: `Inv_H` is a projector on boundary constraints.
- Holo: the **lax** adjunction `ext ⊣ bnd` yields induced projectors
  (`LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda`).
- Port reflection: `CodePort` and the canonical boundary port are equivalent
  presentations of the same satisfaction, so the bootstrapping map is the
  canonical interlingua translation (not a bespoke compiler/transpiler).
  See `LogOS/Ports/Semantic/CanonicalPorts.agda` (definitions) and
  `LogOS/Theorems/Meta/Bootstrapping.agda` (`bootstrap-iso`).
- Safety spine: the boundary/port/guarded-flow architecture is a consequence of
  the “kernel‑only” design choice (no implicit truth/provability). See
  `docs/Meta_Safety.lagda.md` and `LogOS/Theorems/Meta/Safety/*`.
- Kernel-level nucleus theorems: `LogOS/Theorems/Reflection/QuanticNucleus.agda`
  (fixed points form a quantale + quotient factorization, given a nucleus that
  preserves join/multiplication up to `≈`), `LogOS/Theorems/Reflection/NucleusMu.agda`
  (finite/list coverage → closure operator via Kleene μ; `OmegaCPO` required, and
  idempotence uses a Scott‑continuity witness), and `LogOS/Theorems/Reflection/ForcingSheaves.agda`
  (preorder-site coverage: forcing/sheaves = fixed points of a local operator).
No definitional identifications are assumed; see `LogOS/Theorems/Reflection/All.agda`.

Optional graded kernel
----------------------
`LogOS.Kernel.Graded` adds grade‑indexed closure:
- `GradedKernel` replaces `GuardedClosure` with `GradedClosure`.
- `Guard` decodes to `Flow step-grade`; the distinguished fixed point is at `Flow sat`.
  Use the provided promotion/shift lemmas (e.g. `guard-decode≤sat`, `toSatStep`).
- Graded DSL and homs: `LogOS/Kernel/Graded/Endo.agda`, `LogOS/Kernel/Graded/Hom.agda`.
- Re‑exports: `LogOS/Kernel/Graded/All.agda`; boundary lemmas in `LogOS/Theorems/Boundary/Graded/All.agda`.

Necessary Continuity Axioms
---------------------------
ω‑limit reasoning is optional and explicit (`LogOS.Minimal.Truth`):
- `OmegaCPO` supplies `⊥` and `supω` with bound/least laws.
- `FiniteFirst` gives approximants and `Th⋆-as-sup`.
- `cont-ω` is Scott/ω‑continuity of `Flow`.
These are model‑local assumptions (not Choice).

Endomap DSL (Boundary)
----------------------
`LogOS.Kernel.Endo` is a conservative DSL for boundary endomaps:
- `Endo K` packages monotone `Con_bnd → Con_bnd`.
- `_≤₂_` is pointwise refinement; `_∘E_` and whiskering compose refinements.
- `Flow-Endo` packages the guarded step; `idEndo ≤₂ Flow-Endo` and `Flow-Endo ∘E Flow-Endo ≤₂ Flow-Endo`.
- Fixed‑point inequalities (`Th⋆K`/`FlowTh⋆K`, etc.) are exposed for reuse
  (historical `⋆` naming: `Th⋆K` is the distinguished `Th*` witness).
The DSL adds no axioms; it names maps and inequalities already present.

Graded Endomap DSL (Boundary)
-----------------------------
Graded kernels get the same DSL with grades (`LogOS.Kernel.Graded.Endo`):
`Flow-EndoAt`, `ClosureStepAt`, grade‑indexed composition, and promotion via `toSatStep`.

Boundary I/O and Bridge
-----------------------
`LogOS.Boundary.IO` defines the swappable boundary view (`to∂`, `from∂`, `Sat∂`, `sat-coh`).
`boundaryIO` in `LogOS/Kernel/Boundary.agda` derives this from any kernel (graded variant in
`LogOS.Kernel.Graded.Boundary`). `LogOS.Boundary.Semantics` bridges boundary constraints
to external formulas via `Interp` and `Sat∂≈F`.

Free/Initial Constructions
--------------------------
- Free constraint algebra (and indexed variants): `LogOS.Free.All` (`Constraints`, `ConstraintsIndexed`, `ConstraintsOverSig`).
- Initial kernels: `LogOS.Kernel.Initial`, `LogOS.Kernel.Infinite.Initial` (`InitialKernel`, `build`, `build∞`).

Theorems and Meta
-----------------
- Core theorems live in `LogOS/Theorems/Core.agda` (ports, μ/continuity, code facts).
- Meta theorems are conditional (`LogOS.Theorems.Meta.Assumptions` packs; transport in `LogOS.Theorems.Meta.Full`).
- Projectors/fixed points: `LogOS.Theorems.Projective` (instances from `Flow` and `Inv_H`).

Hilbert–Pólya Interface and Faithful Embeddings
----------------------------------------------
`HPInterface` keeps operator reasoning out of the core (`HP/Interface`, `HP/Flow`):
`H`, `Op`, `embed`, and an intertwining law. Faithfulness (`EmbedFaithful`) is explicit,
with helper `embedFaithful-from-retract` (the “identity” special case is just the trivial
retract). Models supply this when using operator‑style bridges.

Diagonalization (Syntactic Pack)
--------------------------------
The Meta layer provides a syntactic diagonalization pack:
`QuoteSubst K` (templates + representability + self‑reference) and `DecodeImp K Pr Op`
(decode‑equality ⇒ provability). `Diagonalization-from-QuoteSubst` yields `diag` and the
two object‑level implications:
`⊢ Imp (diag f) (f (diag f))` and `⊢ Imp (f (diag f)) (diag f)`.
`BoundaryFix` is an explicit, strong monotone fixed‑point assumption; it is *not*
derived from the Kernel or the Endo DSL.

Application Packs (L‑Functions / Spectral Shape)
-----------------------------------------------
Analytic/spectral content is isolated in small application‑level packs:
- Rings: `LogOS/Algebra/Ring.agda`; HP operator interface: `LogOS/Domain/Opacity/NumberTheory/HP/Interface.agda`.
- L‑functions + Selberg: `LogOS/Domain/Opacity/NumberTheory/LFunction/*`.
- Spectral‑style theorems take explicit analytic packs (continuation/product/zeros) and
  keep the core `--safe`.

Set‑Theoretic Baseline
----------------------
No set‑theory commitment: the core is `--safe` and record‑field‑only. Optional ω‑sup selection
is via `LogOS.Axioms.OmegaSup.Interface` (`ChainSup`) and is passed explicitly.

Packs: Structure, Claims, Boundaries
-----------------------------------
The curated packs are thin wrappers over the kernel. Each pack makes its assumptions
explicit, states a clean claim, and avoids leaking application‑specific axioms into
the core. The hook is kernel polymorphicity: the same kernel supports distinct
semantic stories without changing the foundational definitions.

- ZFC pack (`LogOS/Packs/ZFC/All.agda`)
  - Claim: WF‑graph semantics yield definable ZF (+Infinity), with optional upgrades.
  - Boundary: Choice and full Replacement/Separation are explicit add‑ons.
  - Interest: shows set‑theoretic semantics without embedding classical axioms.

- Universality pack (`LogOS/Packs/Universality/All.agda`)
  - Claim: universal computation + transport theorems + information/physics bounds.
  - Boundary: results are conditional on explicit model/adapter assumptions.
  - Interest: unifies computation and physics under one kernel interface.

- Opacity pack (`LogOS/Packs/Opacity/Experimental/All.agda`)
  - Claim: observability/diagonal barriers as explicit records; nucleus/fixed‑point
    reasoning for what can be observed at the boundary.
  - Boundary: application claims are conditional; analytic content stays isolated.
  - Interest: opacity is kernel‑native (Flow + Projector), so it composes across domains.

- Complexity pack (`LogOS/Packs/Complexity/Experimental/All.agda`)
  - Claim: verification vs search separation as graded‑flow interfaces; classical
    alignment is an adapter, not an axiom.
  - Boundary: separation is conditional on explicit hardness/physics assumptions.
  - Interest: resource‑bounded verification becomes a boundary phenomenon.

- Agents pack (`LogOS/Packs/Agents/All.agda`)
  - Claim: agents as open systems via sockets/ports/contracts; monitoring/auditing
    is expressed in kernel endomaps.
  - Boundary: safety/audit conclusions rely on explicit opacity assumptions.
  - Interest: the kernel already *is* an agent‑like system, so the pack is thin.

Reusable libraries live under `LogOS/Domain/*` and `LogOS/Algebra/*`
(HP interface, braiding helpers, ZF/ZFC adapters). Tests: `Tests/All.agda`.
Examples live under `LogOS/Domain/*/Examples/*`.

Kernel Polymorphicity: Four Views
--------------------------------
The kernel admits multiple semantic readings without altering its definitions:
- Multi‑institution (model‑theoretic): `docs/Views/MultiInstitution.lagda.md`
- 3‑level HoTT-style positioning: `docs/Views/HoTT_3Level.lagda.md`
- Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
- Observer semantics (physics‑aligned): `docs/Views/ObserverSemantics.lagda.md`

Honesty and Scope
-----------------
Core theorems are `--safe` and use no global postulates. Any extra axioms must be isolated
in opt‑in packs.

Regularization & Renormalization (Heat‑Kernel View)
--------------------------------------------------
Interpretation note: the core supports a “regularize → renormalize” reading.
`Flow` is a closure step, projectors/nuclei give fixed‑point truth, and HP/opacity bridges
transport stability via explicit embeddings. This is semantic guidance, not an axiom.

Axioms–Theorems Index (Exact Dependencies)
-----------------------------------------
Dependency details live with the theorems. Key entrypoints:
- `LogOS/Theorems/Laws/FiniteKernel/*` (S/H ports, free folds)
- `LogOS/Theorems/Boundary/*` (μ, continuity, guarded/reflective facts)
- `LogOS/Theorems/Code/*` (decode‑level lemmas)
- `LogOS/Theorems/Meta/*` (conditional results + assumption packs)

Boundary Fixed Points (Non‑vacuous)
-----------------------------------
`BoundaryFix` (assumption pack) gives a fixed point for every monotone endomap.
`BoundaryFixFromScott` wraps Scott fixed points; a one‑point boundary gives a trivial instance.

Projective Perspective (Fixed‑Point Logic)
-----------------------------------------
`Projector` is an inflationary, idempotent‑lax closure; fixed points form a sub‑preorder
(and a sub‑partial‑order if you additionally assume antisymmetry via `PartialOrder`).
Instances: `Flow` (G‑tier) and `Inv_H` (H‑tier).

Local vs Global Truth — Fixed‑Point Strengthening (with ω‑sups)
--------------------------------------------------------------
Guarded fixed points are inequalities by default. With `OmegaCPO` + `FiniteFirst`,
μ‑induction (least pre‑fixed‑point) holds and `FiniteFirst.cont-ω` supplies Scott/ω‑continuity;
with antisymmetry you can read the leastness at the level of equality.
Optional ω‑sup selection uses `LogOS.Axioms.OmegaSup.Interface`.

Module References (Source Paths)
--------------------------------
- Signature: `LogOS/Base/Signature.agda`
- Adapter: `LogOS/Minimal/Adapter.agda`
- Worlds: `LogOS/Minimal/World.agda`
- Constraints: `LogOS/Minimal/Con.agda`
- Lax Adjunction: `LogOS/Minimal/Adjunction.agda`
- Truth (S/H/G): `LogOS/Minimal/Truth.agda`
- Kernel: `LogOS/Kernel.agda`
- Boundary I/O: `LogOS/Boundary/IO.agda`, `LogOS/Boundary/Semantics.agda`, `LogOS/Kernel/Boundary.agda`
- Kernel Hom: `LogOS/Kernel/Hom.agda`
- Free constraints: `LogOS/Free/Constraints.agda`
- Initial kernel: `LogOS/Kernel/Initial.agda`
- Proven theorems: `LogOS/Theorems/Laws/FiniteKernel/S.agda`, `LogOS/Theorems/Laws/FiniteKernel/H.agda`, `LogOS/Theorems/Boundary/Mu.agda`, `LogOS/Theorems/Boundary/Continuity.agda`, `LogOS/Theorems/Code/Core.agda`, `LogOS/Theorems/Boundary/Guarded.agda`
- Aggregators: `LogOS/Ports/All.agda`, `LogOS/Adapters/All.agda`
- Meta (conditional): `LogOS/Theorems/Meta/Assumptions/Core.agda`, `LogOS/Theorems/Meta/Assumptions/Diagonal.agda` (umbrella: `LogOS/Theorems/Meta/Assumptions.agda`), `LogOS/Theorems/Meta/Full.agda`, `LogOS/Theorems/Meta/Rice.agda`, `LogOS/Theorems/Meta/Tarski.agda`, `LogOS/Theorems/Meta/Lob.agda`, `LogOS/Theorems/Meta/Godel.agda`
- Helpers (continuity): `Tests/ContinuityOne.agda`

Conditional applications (brief, honest)
---------------------------------------
Some packs include optional application routes. They remain *conditional* and live
outside the core: opacity provides spectral adapters and nucleus bridges; complexity
provides graded verification/search interfaces. These are interfaces to structure
assumptions, not proofs of external analytic or combinatorial claims.
Further narrative: `docs/Applications/Opacity.lagda.md`, `docs/Applications/Complexity.lagda.md`.
ZF in the Limit (Cumulative Hierarchy)
--------------------------------------
- Forcing-like closure: boundary `Flow` is a nucleus/closure operator; the DSL requires
  membership to respect it, and `StageToCH-fromCH-μFlow` optionally replaces the distinguished
  witness with the Kleene μ of `Flow` when ω-sup data is supplied.
- Flow surface: `LogOS/Domain/ZFC/SetTheory/Dsl.agda` packages any `ZFAxioms` instance with a boundary interpretation (`realise`) and exposes the lemmas showing that membership/equality respect the canonical global step `Flow`. Downstream models instantiate the DSL first, then call `surfaceToZFAxioms` to retrieve the classical pack with these boundary lemmas in tow.
- Interface: `LogOS/Domain/ZFC/SetTheory/LimitPack.agda` defines `CumulativeHierarchy K` (colimit universe) and `toZFAxioms` (adapter to `ZFAxioms`).
- Packs for stages: `LogOS/Domain/ZFC/SetTheory/Cumulative.agda` declares the stage‑level packs (`StageIndex`, `StageSet`, `SuccessorClosure`, `LimitClosure`, `RankBounding`, `DecodeBridge`) and bundles them in `StageToCH` with a provided `CumulativeHierarchy`, plus the boundary realisation witnesses required by the Flow surface (`realise∞`, `mem⇒flow∞`, `eq⇒realise∞≡`, `tf-stable∞`). `StageIndex` records comparability data (a canonical base successor `zeroStage`, a “join” operation, and `succAbove`) so transfinite towers can be glued into a single hierarchy; `StageSet` is universe-polymorphic and exposes stage‑local extensionality/equality fields so global proofs can be lifted.
- Stage-to-DSL adapter: `LogOS/Domain/ZFC/SetTheory/CumulativeSurface.agda` defines `stageToSurface`, consuming any such `StageToCH` bundle and producing a `ZFDsl` witness. A minimal, LogOS-native adapter `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda` turns any already-built `CumulativeHierarchy K` into a `StageToCH K` (constant stages, canonical fixed-point witness `Th⋆K` realisation). If a model additionally supplies a boundary `OmegaCPO` + `FiniteFirst` witness for Flow, `StageToCH-fromCH-μFlow` provides the corresponding μ-based “least (pre)fixed point” realisation at infinity (in the boundary preorder). `LogOS/Domain/ZFC/SetTheory/FromZFAxioms.agda` provides the parallel adapter `ZFAxioms K → CumulativeHierarchy K`.
- WF-graph route (core): `LogOS/Domain/ZFC/WFGraph/Model.agda` + `LogOS/Domain/ZFC/WFGraph/ZFC.agda` implement “sets as well-founded membership graphs”, producing definable-ZF(+Infinity) and (optionally) full `ZFAxioms`. `LogOS/Domain/ZFC/WFGraph/Surface.agda` is the one-stop façade: `Definable` exposes the definable pack, and `Full` exposes `zf`, `CH`, `stageToCH`, and `surface`. ZFC is obtained by adding an explicit AC witness (`LogOS/Domain/ZFC/SetTheory/ChoiceAxiom.agda`) to `ZFCAxioms` (`LogOS/Domain/ZFC/SetTheory/Pack.agda`).
- Derived set constructors: `LogOS/Domain/ZFC/SetTheory/Derived.agda` collects small “derived” operations (like `singleton` and binary union) over any `ZFAxioms` instance to keep downstream developments lean.
- Membership graphs (supplementary): `Data/Graph.agda` defines the canonical graph datatype (vertex carrier + adjacency relation). `LogOS/Domain/ZFC/Supplementary/HF/HFGraph.agda` interprets the HF universe through that graph lens (vertices = HF sets, edges = membership). This is useful for rewriting-style experiments but is not on the core WF-graph mechanisation path.
- Algebraic graphs: `LogOS/Algebra/GraphSurface.agda` lets any `FiniteGraph` (adjacency matrix over a ring) supply a pure adjacency predicate and immediately exposes it as a `Data.Graph`. This is the natural bridge for Ihara/spectral packs (including opacity/observability applications) so they can share the same graph semantics as the HF/cumulative hierarchy side without duplicating definitions.
- HF-based components live under `LogOS/Domain/ZFC/Supplementary/HF/*`.
- No hidden assumptions: construct `CH` from explicit packs (successor/limit closure; Scott continuity + ω‑sup selection on boundary preorders; rank bounding for Separation/Replacement). Then use `toZFAxioms` to expose a full ZF interpretation (and optionally add set‑theoretic AC separately). This mirrors the standard cumulative hierarchy argument and leverages the logic’s fixed‑point continuity infrastructure.
