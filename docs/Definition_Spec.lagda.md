<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Foundational Definition (Reference Spec)

```agda
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
import LogOS.Kernel.Initial
import LogOS.Kernel.Infinite.Initial
import LogOS.Theorems.Projective
import LogOS.Theorems.Meta.Assumptions
```

For a newcomer-friendly architecture overview, see `docs/Definition.lagda.md`.

Overview
--------
This literate file presents the exact, research‑grade definition of the LogOS
foundational core as implemented in this repository. It is a faithful summary
of the records and laws present in the code, grouped by purpose. All “axioms”
are explicit record fields; proofs build only on those fields. Where continuity
or fixpoint properties are needed, they are supplied as model‑local assumptions
packaged in records.

Conventions and Notation
------------------------
- Universe levels: all records are level‑polymorphic in `ℓ : Level`; derived types
  live in `Set (lsuc ℓ)` when they contain fields ranging over `Set ℓ`.
- Equality: when we write “equality”, we mean propositional equality `_≡_` from
  `Data.Relation.Binary.PropositionalEquality` (no definitional equality is assumed).
- Decode‑level equality: for a given kernel `K`, open `LogOS.Syntax.Eq.ForKernel K`
  to use `_≃K_` as a dedicated alias for `decode γ₁ ≡ decode γ₂`.
- Preorders vs partial orders: all order structures in this core are preorders
  (`refl`, `trans`). Antisymmetry (to obtain partial orders) is optional and is
  provided via separate records when needed (see `PartialOrder` in `LogOS/Minimal/Con.agda`).
- Bi‑implication: coherence fields use `LogOS.Syntax.Prop._↔_` (pairs of functions),
  not definitional equalities. This choice is intentional and explicit.
- Bottom/negation discipline: import `LogOS.Syntax.Prop` for bottom `⊥` and
  negation `¬_ = _ → ⊥` and reuse them consistently across the repo.

Universe/Prelude
----------------
- Canonical import: `open import LogOS.Prelude` (levels, propositional equality,
  and minimal shims for `ℕ`, `Σ`, `×`, `⊎`, and `⊤`), plus `Topℓ : Set ℓ`.

Signature
---------
Primitive carriers and operations are collected in `LogOS.Base.Signature`.
We do not re‑define them here; the actual fields are:
- `Sorts`: `Iface`, `Cosp`, `∂Cosp`
- `CospanOps`: `src`, `tgt`, `idC`, `_∘C_`, `_⊕C_`, `_⊗C_`
- `BoundaryOps`: `src∂`, `tgt∂`, `id∂`, `_∘∂_`, `_⊕∂_`, `_⊗∂_`, `ext`, `bnd`
- `LogOSSignature`: bundles the above as `sorts`, `cospanOps`, `boundaryOps`

Adapter and Worlds (S/H/G)
--------------------------
Quantitative/time structure is kept minimal in `QAdapter`, with fields:
`Scale`, `_≤s_`, `_·_`, `e`, `_≤p_`, `Time`, `_+_`, `zero`, `τ`.
Worlds are tiered (`LogOS.Minimal.World`):
- `WorldS = Cosp`
- `WorldH Q` with fields `_≤ctx_`, `WFlow`, `wflow-refl`, `wflow-trans` (internally renaming
  the `QAdapter` operations to `Scl`, `_∙_`, `ε`)
- `WorldG Q = WorldH Q` (guardedness lives in truth).

`LogOS.Minimal.Con` defines:
- `ConPoset`: `Con`, `_⊑_`, `refl`, `trans`
- `BulkBoundary`: `bulk`, `bnd`
`LogOS.Minimal.Adjunction` defines:
- `MonoidalPoset`: `_⊗_`, `I`, `mono⊗`
- `LaxAdjunction`: `ext`, `bnd`, `unit-lax`, `counit-lax`
- `LaxMonoidalAdjunction`: `core`, `ext-⊗-lax`, `ext-I-lax`, `bnd-⊗-lax`, `bnd-I-lax`

Truth Interfaces (S/H/G)
------------------------
Strict layer (S), homotypical layer (H), and guarded layer (G) are packaged as records.
`LogOS.Minimal.Truth` defines:
- Strict layer: `StrictTruth.StrictLayer` with `Sat_S`, `_⊢S_`
- Homotypical layer: `HomotypicalTruth.HLayer` with `Sat_H`, `mono-Con`, `mono-ctx`
  and `HomotypicalTruth.Invariance` with `Inv_H`, `infl`, `idemp-lax`
- Guarded layer: `GuardedTruth.GuardedClosure` with `Flow` (closure/nucleus step),
  `mono`, `infl`, `idemp-lax`, `Th*`, `Th*-fixed`
- Optional graded guarded layer: `GuardedCore.GradedClosure` with grade‑indexed
  `Flow`, grade monotonicity `mono-grade`, lax composition `comp-lax`, a saturation
  grade `sat` (with `sat-top`, `infl-sat`, `idemp-sat`), and fixed point `Th*`.
  Transport interfaces live in `GuardedCore.GradeHom`, `GradedFlowHom`, and
  `GradedFlowHomWithGrade`.
- Optional structure: `GuardedTruth.OmegaCPO` with `⊥`, `isBot`, `supω`, `ub`, `least`, and
  `GuardedTruth.FiniteFirst` with `approx0`, `approxS`, `base`, `step`, `Th⋆-as-sup`, `cont-ω`
- Naming note (fixed points): `Th*` is the Kernel’s distinguished fixed-point witness (in preorder form via `Th*-fixed`).
  When `OmegaCPO` + `FiniteFirst` are present, `Th⋆` names the ω‑supremum of finite approximants; downstream theorems
  relate these presentations (e.g. `Th*-as-sup-K`).
- Tensor guarantees: `LogOS.Kernel.TensorEndo` exposes canonical tensor endomaps on the
  boundary (`_⊗ᵣ_`, `_⊗ₗ_`) together with Flow refinements
  (`Flow⊗-endo-right`, `Flow⊗-endo-left`, `Flow⊗-infl-≤₂`). Downstream models rely on these lemmas to
  keep all whiskering/monotonicity reasoning uniform.

Best‑practice notes
- All monotonicity is explicit (no hidden principles beyond equality + provided fields).
- Fixed points stay in preorder land (`Th*-fixed` are inequalities, not equalities).

Kernel (Integrated Model)
-------------------------
The Kernel record integrates S/H/G truth and code reflection into a single structure
over your signature and adapter. Field names and roles are:

- World and constraints
  - `HWorld` : world structure for the H‑tier (`_≤ctx_`, `WFlow`, `wflow‑refl`, `wflow‑trans`).
  - `BB`     : `BulkBoundary` (bulk and boundary preorders).
  - `MBulk`  : `MonoidalPoset` on bulk constraints.
  - `MBnd`   : `MonoidalPoset` on boundary constraints.
  - `Holo`   : `LaxMonoidalAdjunction BB MBulk MBnd` (ext ⊣ bnd, lax monoidal laws).

- H‑tier truth and invariance (depend on `HWorld`)
  - `HTruth` : `HomotypicalTruth.HLayer BB` with `Sat_H`, `mono‑Con`, `mono‑ctx`.
  - `HInv`   : `HomotypicalTruth.Invariance BB` with `Inv_H`, `infl`, `idemp‑lax`.

- Boundary view of H‑satisfaction and S/H coherence
  - `Sat_H_bnd` : boundary presentation of H‑satisfaction.
  - `sat-coh`   : for all `w : Cosp` and `c : Con_bnd`, a bi‑implication
                  between `HLayer.Sat_H HTruth w c` and `Sat_H_bnd (bnd w) c`.

- S‑tier strict layer and coherence
  - `Fml`    : carrier of formulas at the S‑tier.
  - `Strict` : `StrictTruth.StrictLayer Fml` with `Sat_S` and entailment shape `_⊢S_`.
  - `TransH` : translation from S‑formulas to boundary constraints.
  - `coh‑LH` : for all `w, φ`, a bi‑implication between `Sat_S w φ` and
               `HLayer.Sat_H HTruth w (TransH φ)`.

- G‑tier (guarded) closure on boundary constraints
  - `GTruth` : `GuardedTruth.GuardedClosure (BulkBoundary.bnd BB)` with
               `Flow`, `mono`, `infl`, `idemp‑lax`,
               `Th*`, `Th*‑fixed`.

- Code/reflection (decode‑level interface)
  - `Code`   : code type; `encode : Con_bnd → Code`; `decode : Code → Con_bnd`.
  - `decode∘encode` : decode (encode c) ≡ c.
  - `Guard`         : guarded step on code; `Body` : code‑level body.
  - `FlowCode`      : derived helper (`λ γ → Guard (Body γ)`) provided for convenience.
  - `guard‑decode`  : decode (Guard γ) ≡ Flow (decode γ).
  - `γ*`, `γ*‑guard`, `decode‑γ*` : a code‑level witness for `Th*`. The `γ*‑guard`
    field is stated at **closure strength** (as preorder inequalities after
    decoding), not as a definitional code equality.
  - `reify`, `reify‑decode` : observational reification at decode‑level.
  - `Body∂`, `body‑decode` : boundary view of the code body with decode‑level coherence.

Optional graded kernel
----------------------
`LogOS.Kernel.Graded` provides a graded extension of the kernel interface:
- `GradedKernel` replaces the guarded closure with a grade‑indexed `GradedClosure`.
- Adds `step-grade` (code‑level guard grade); `step≤sat` is derived from `sat-top`
  to align steps with saturation.
- Important: `Guard` decodes to **`Flow step-grade`**, while the distinguished
  fixed point `Th*` is characterised at **`Flow sat`**. Do not treat these as
  interchangeable. The library exposes derived “grade shift” lemmas (e.g.
  `guard-decode≤sat`) and explicit promotion helpers (`promoteStep`, `toSatStep`)
  so the shift is always witnessed.
  If your model happens to satisfy `step-grade ≡ sat`, grading can be forgotten
  and recover an ordinary kernel via `LogOS.Kernel.Graded.ToKernel.asKernel`.
- `LogOS/Kernel/Graded/Endo.agda` mirrors the endomap DSL and adds grade‑indexed
  closure steps; `LogOS/Kernel/Graded/Hom.agda` provides graded homs, including
  grade‑reindexing via `GradeHom`.
- `LogOS/Kernel/Graded/All.agda` re‑exports the graded surface and graded boundary theorems.
- Standard graded boundary lemmas live in `LogOS.Theorems.Boundary.Graded.*` (notably
  `QuickWins`): step iteration bounds and closure absorption (`step-iteration≤sat`,
  `saturation-absorption`, `step-power-law`).

Necessary Continuity Axioms
---------------------------
Some meta‑theorems (μ‑induction over approximants, ω‑limit commuting facts, “infinite
kernel” fixed‑point reasoning) require an explicit continuity interface at the model
boundary. This is provided by the optional ω‑CPO/finite‑first layer in
`LogOS.Minimal.Truth`:
- `GuardedTruth.OmegaCPO` supplies a chosen bottom `⊥` and a chosen supremum `supω`
  for ω‑chains, together with the universal bound/least laws (`ub`, `least`).
- `GuardedTruth.FiniteFirst` supplies canonical approximants `approxS` and a proof
  that `Th⋆` is their supremum (`Th⋆-as-sup`).
- `cont-ω` is the necessary continuity axiom: it asserts that `Flow` is (lax)
  compatible with the chosen ω‑suprema.
- Textbook names: `cont-ω` is Scott/ω‑continuity of `Flow`; `Th⋆-as-sup` is the
  Kleene approximation theorem (least fixed point as ω‑supremum of approximants).

This should be read as “provide the continuity data you need”, not as the set‑theoretic
Axiom of Choice. It is an explicit, model‑local assumption used exactly where the
development wants ω‑limits to interact well with the global step.

Endomap DSL (Boundary)
----------------------
For any kernel `K`, we expose a tiny, conservative DSL for boundary endomaps:
- `LogOS.Kernel.Endo.Endo K` packages a monotone map `fn : Con_bnd → Con_bnd`.
- Pointwise refinement between maps: `f ≤₂ g := ∀ c → fn f c ⊑ fn g c`.
- Identity, composition, and preservation of refinement under composition are
  provided as simple helpers (`idEndo`, `_∘E_`, `whisker-left`, `whisker-right`).
- The global truth step is presented as an endomap `Flow-Endo K`, together with
  the canonical refinements derived from the guarded closure fields:
  `idEndo K ≤₂ Flow-Endo K` (inflation) and `(Flow-Endo K ∘E Flow-Endo K) ≤₂ Flow-Endo K`
  (lax idempotence).
- Canonical fixed-point witnesses: `Th⋆K`, `FlowTh⋆K`, `Th⋆≤FlowTh⋆`, and
  `FlowTh⋆≤Th⋆` expose the guarded μ as first-class inequalities. `FlowTh⋆≡Th⋆`
  (alias `fixedpoint-eq-under-antisym`) upgrades them to an equality under
  `BulkBoundaryPO`. Additional helper lemmas
  (`Flow≤f→Th⋆≤fTh⋆`, `f≤Flow→fTh⋆≤Th⋆`, `Flow≃f→fTh⋆≡Th⋆`) let any DSL endomap
  piggyback on those guarantees using only `_≤₂_` witnesses, so extension
  packs stay modular and rely purely on whiskering-friendly inequalities.

This DSL does not add any axioms; it simply names maps and inequalities that are
already available from the guarded truth layer and boundary poset. It makes it
convenient to compose arguments (e.g., via whiskering) and to state “2‑cell‑like”
facts using the preorder discipline (`≤₂` as pairs of inequalities when needed).

Graded Endomap DSL (Boundary)
-----------------------------
For graded kernels, the same DSL is available with grade tracking:
- `LogOS.Kernel.Graded.Endo` provides `Flow-EndoAt`, grade‑indexed `ClosureStepAt`,
  and composition `_∘StepAt_`/`_thenStepAt_` (grades compose by `g₁ · g₂`).
- The ungraded API is recovered via `toSatStep`, which promotes any grade to the
  saturation grade `sat`.

Boundary I/O and Bridge
-----------------------
- Boundary I/O (swappable): `LogOS.Boundary.IO` packages the external boundary view over a given
  world and H‑truth with fields `to∂`, `from∂`, `Sat∂`, and a coherence equivalence
  `sat-coh : _↔_` relating H‑tier satisfaction to the boundary semantics.
- Default boundary I/O from any kernel: `LogOS.Kernel.Boundary.boundaryIO` derives a
  `BoundaryIO` instance using the kernel’s `ext`, `bnd`, and `Sat_H_bnd` fields.
- Default boundary I/O from any graded kernel: `LogOS.Kernel.Graded.Boundary.boundaryIO`.
- Boundary bridge to external logics: `LogOS.Boundary.Semantics` introduces an external
  boundary `Form` with `SatF` and an interpretation `Interp : Con_bnd → Form`, together with
  an equivalence `Sat∂≈F : _↔_` to transport H‑tier results into external formulas.

Free/Initial Constructions
--------------------------
- Free constraint algebra: `LogOS.Free.Constraints`
  - syntax: `Con∂`, `Conb`; preorders: `_≤∂_`, `_≤b_`
  - free structures: `BBfree`, `MBulkfree`, `MBndfree`, `Holofree`; `FreeConAlg`
  - folds: `interp∂`, `interpb`, `fold≡`; initial interface: `InitialConAlg`, `initialConAlg`
- Initial kernel: `LogOS.Kernel.Initial`
  - record: `InitialKernel` with `FreeK`, `foldK`, `unique`
  - builder: `build`; hom helpers: `foldFlow`, `foldFlow-auto`, `foldFlow-auto-ineq`, `foldFlow-build-auto`

Theorems and Meta
-----------------
- Proven theorems (Ports, μ/Continuity, Guarded code facts) are derived from the
  records above. See `LogOS.Theorems.*`.
- Meta theorems are conditional and depend on assumption packs: see
  `LogOS/Theorems/Meta/Assumptions/Core.agda` and `LogOS/Theorems/Meta/Assumptions/Diagonal.agda`
  (umbrella re-export: `LogOS/Theorems/Meta/Assumptions.agda`) and transport utilities in
  `LogOS/Theorems/Meta/Full.agda`. The transport lemma itself is textbook (decidability
  pulls back along reductions); any diagonalisation/fixed‑point strength lives in the
  model‑local proof/assumption packs.
- Projective kit (fixed‑point perspective): `LogOS/Theorems/Projective.agda` packages
  a generic `Projector` on any constraint poset, with a `Fixed` construction
  that exposes the poset of fixed points. Instances arise from:
  - Guarded closure (G‑tier): `Projective.ForG.fromGuarded` builds a projector
    from any `GuardedTruth.GuardedClosure` (the global `Flow` acts as a projector).
  - H‑tier invariance on boundary posets: `Projective.ForH.fromInvariance` builds
    a projector from `HomotypicalTruth.Invariance`.

Hilbert–Pólya Interface and Faithful Embeddings
----------------------------------------------
The HP interface (`LogOS/Domain/Opacity/NumberTheory/HP/Interface.agda`, `LogOS/Domain/Opacity/NumberTheory/HP/Flow.agda`) keeps operator‑style
reasoning out of the core. A kernel‑local `HPInterface` provides:
- an ambient space `H`
- an operator `Op : H → H`
- an embedding `embed : Con_bnd → H`
- an intertwining law with the global flow

Faithfulness of the embedding is an explicit assumption via `EmbedFaithful`, stating
that equality in `H` reflects back to equality of boundary constraints. For common
cases we offer small builders:
- `embedFaithful-from-retract` (provide a retraction π with π ∘ embed ≡ id)
- `embedFaithful-id` (identity‑like embeds)

Model packs import this extension and pass an `EmbedFaithful` instance explicitly to bridge
theorems (e.g., GRH adapters), keeping the architecture hexagonal and the core clean.

Diagonalization (Syntactic Pack)
--------------------------------
To keep category‑theory semantics out of the core while making diagonalization
“almost obvious,” the Meta layer provides a small syntactic pack plus a thin
decode→provability bridge:

- `QuoteSubst K` (pure syntax over a kernel `K`):
  - `Code₁` (single‑hole templates), `inst : Code₁ → Code → Code` (plugging)
  - `representable : (Code → Code) → Σ Code₁ (λ u → ∀ γ → decode (inst u γ) ≡ decode (f γ))`
  - `self : (u : Code₁) → Σ Code (λ s → decode s ≡ decode (inst u s))`
- `DecodeImp K Pr Op` (local reflection):
  - `from-decode≡→imp : decode φ ≡ decode ψ → ⊢ (Imp φ ψ)`

From these two, the record `Diagonalization K Pr Op` is constructed by
`Diagonalization-from-QuoteSubst`, yielding the classical `diag` together with
the two implications `⊢ diag f → f (diag f)` and `⊢ f (diag f) → diag f`.

Note: the boundary fixed‑point assumption `BoundaryFix` is explicit and strong:
it asks for a fixed point (up to the boundary preorder) for every **monotone**
endomap on boundary constraints. This is the textbook Knaster–Tarski/Scott shape
recast in LogOS’ preorder discipline (`c ⊑ f c × f c ⊑ c`), and it is not derived
from the Kernel interface.
Do not confuse this with the Endo DSL (`LogOS.Kernel.Endo`), which packages monotone endomaps and uses preorder
fixed‑point laws/inequalities (not arbitrary extensional fixed points) as its default notion of “μ”.

Application Packs (L‑Functions / GRH Shape)
------------------------------------------
The Minimal and Kernel definitions are agnostic about classical analysis, but the
repository includes an L‑function abstraction suitable for Selberg/GRH‑style reasoning.
This is intentionally packaged as separate “application‑level” records so that
all analytic assumptions stay explicit, keeping the proven core `--safe`.

- Arithmetic core (rings/fields):
  - Minimal ring interface: `LogOS/Algebra/Ring.agda` (`Ring`), used as the base carrier for L‑function domains/codomains.
  - Hilbert–Pólya interface (kernel‑tied, ring‑free): `LogOS/Domain/Opacity/NumberTheory/HP/Interface.agda` (`HPInterface`).

- L‑function abstraction:
  - `LogOS/Domain/Opacity/NumberTheory/LFunction/Core.agda` defines `LFunction` with fields
    `In : Carrier → Set`, `L : Carrier → Carrier`, `Gamma : Carrier → Carrier`,
    and parameters `Q, eps` (conductor‑ and epsilon‑like).
  - `LambdaFE` is the textbook‑aligned primary interface: a completed functional
    equation for `Λ(u) = Gamma u * L u` and domain closure under `mirror`.
  - `LZ-FE` packages an “uncompleted” functional equation on `L` over `In`.
  - `GammaSym` packages symmetry and domain‑closure for the Gamma factor.
  - `LambdaFE-from-LZ+Gamma` derives the completed functional equation for
    `Λ(u) = Gamma u * L u` and `mirror u`.
  - `LogOS/Domain/Opacity/NumberTheory/LFunction/Selberg.agda` wraps the above as a `SelbergPack` record.

- Towards a “fully worked” GRH example (structure checklist):
  - A model for a field akin to ℂ (carrier, +, *, 0, 1, inverse), and a norm/absolute value.
  - A domain predicate `In s` capturing the analytic region(s) of interest.
  - L‑function data: Dirichlet/Euler product on Re(s)>1 (as a definitional interface or assumption).
  - Functional equation with conductor Q, epsilon ε, and Gamma factors (as in `SelbergPack`).
  - Analytic continuation (entire or meromorphic, with at most simple poles) stated as assumptions.
  - Nontrivial zeros interface and a GRH predicate: “every nontrivial zero lies on Re(s)=1/2”.
  - Optional growth/zero‑free regions for explicit bounds.

In this library’s design, the above are stated as small records/assumptions local to the
application. For example, an `AnalyticPack` could list continuation, product, and growth; a
`ZerosPack` could define “nontrivial zero” and the GRH predicate. A GRH‑style theorem would then
take these packs as parameters and produce conclusions about the model, keeping the proven core
unaffected and axioms explicit.

Set‑Theoretic Baseline
----------------------
We make no commitment to a particular set theory. The proven `--safe` modules depend only on
explicit record fields. Analysis‑heavy results (like GRH) are kept as opt‑in packs; an opt‑in
ω‑sup selection interface (domain-theoretic, not ZFC’s AC) is available via `LogOS.Axioms.OmegaSup.Interface` (`ChainSup`) and is passed explicitly to models that need it.

Reusable Libraries (Packs)
-------------------------
Reusable, conservative libraries live under `LogOS/Domain/*` and `LogOS/Algebra/*` and depend only on the core:
- `LogOS/Domain/Opacity/NumberTheory/HP/*` — operator interface + Flow transport (no ring required)
- `LogOS/Algebra/Braiding.agda` — lax braiding and Flow monoidality helpers
- `LogOS/Domain/SetTheory/*` — ZF/ZFC adapters (cumulative hierarchy + adapter; AC is a separate statement)
Testing: `Tests/All.agda` aggregates these modules for typechecking.
Guideline: keep adapters thin. Domains import only what they need, and `LogOS/Models/*` provides recommended wrappers over `LogOS/Domain/*`.
This 1.0 snapshot ships no demo modules; narrative examples live in `docs/` and regression coverage in `Tests/`.

Honesty and Scope
-----------------
No hidden postulates are used in the proven theorems: the core theorems are `--safe`
and depend only on explicit record fields (e.g., Scott‑continuity via `FiniteFirst.cont-ω`).
This production snapshot ships with **no global postulates**; additional axioms (if ever added)
must be isolated in clearly marked, opt‑in modules/packs.

Regularization & Renormalization (Heat‑Kernel View)
--------------------------------------------------
At a high level, the core behaves like a disciplined “regularize → renormalize” pipeline for logic:

 - Flow as time‑step regularizer
  - The guarded closure step is `GuardedTruth.GuardedClosure.Flow : Con → Con`:
    an inflationary, idempotent‑lax endomap (a closure step).
  - Iteration `Th*` is the ω‑limit of regularization steps. With `OmegaCPO` + `FiniteFirst.cont-ω`,
    this is a canonical least fixed point in the preorder sense.

- Projectors (nuclei) as renormalization
  - `LogOS.Theorems.Projective.Projector` packages closure operators (nuclei) on constraint posets.
  - Fixed points of a projector/nucleus are the “renormalized truths” (stable under the chosen closure).

- Operator semantics = heat‑kernel generalization
  - `LogOS/Domain/Opacity/NumberTheory/HP/Flow.agda` exposes a tight correspondence: there exists an operator `Op` on a host space
    and an embedding `embed` with `embed ∘ Flow ≡ Op ∘ embed`.
  - This realizes the heat‑kernel intuition: the logical closure step is mirrored by a linear (or affine)
    operator step; fixed points commute via the embedding (with faithfulness).

- Finite regulators and limits
  - Finite truncations (finite regulator instances) act as concrete regulators.
- Limit wrappers (`LogOS/Domain/Opacity/Applications/GRH/HPGRHLimit.agda`, `LogOS/Domain/Opacity/Applications/GRH/HPGRHLimitOmegaSup.agda`) use ω‑sup‑built `OmegaCPO` to pass from finite
    fixedness to a limit fixedness, then discharge a spectral clause at the limit.

- Why this matters for GRH‑style reasoning
  - Operator bridge: postulate “zeros ⇒ Op‑fixed” and “Op‑fixed ⇒ OnLine”; Flow transports stability.
  - Categorical bridge (operator‑free): pick a nucleus/projector P; postulate “zeros ⇒ P‑fixed” and
    “P‑fixed ⇒ OnLine”. Both patterns are regularization‑first, renormalization‑as‑fixed‑points.

This perspective is strictly internal: the Minimal/Kernel core proves only closure/fixed‑point theorems from
explicit fields. Any analytic content (e.g., ζ/ξ) is introduced via small, opt‑in assumption packs, so the
heat‑kernel analogy remains a clean semantic layer rather than a hidden axiom.

Axioms–Theorems Index (Exact Dependencies)
-----------------------------------------
This index maps each theorem group to the record fields it relies on.

- Ports (S↔H) — `LogOS/Theorems/Laws/FiniteKernel/S.agda`
  - Requires: `Kernel.coh-LH : _↔_` (S↔H coherence), `Kernel.Strict`, `Kernel.TransH`.
  - Output: `S→H`, `H→S` transport lemmas.

- Free algebra fold and completeness — `LogOS/Theorems/Laws/FiniteKernel/H.agda`
  - Requires: Free constraint algebra (`FreeConAlg`) and fold (`interp∂`, `interpb`, `fold≡`) from `LogOS/Free/Constraints.agda`.
  - Output: `fold∂-preserves`, `foldb-preserves`, `complete∂`, `completeb`.

- Guarded μ — `LogOS/Theorems/Boundary/Mu.agda`
  - μ‑unfold: Requires only `Kernel.GTruth` (i.e., `GuardedTruth.GuardedClosure`), specifically `Th*-fixed`.
    - Output: `μ-unfold-left`, `μ-unfold-right` inequalities.
  - μ‑induction: Additionally requires `OmegaCPO` and `FiniteFirst` instantiated at `BulkBoundary.bnd (Kernel.BB K)`.
    - Output: `μ-induction-K` (aliases: `park-induction-K`, `least-prefixed-point-K`).

- Continuity wrappers — `LogOS/Theorems/Boundary/Continuity.agda`
  - Requires: `OmegaCPO` and `FiniteFirst` at `BulkBoundary.bnd (Kernel.BB K)` with `Kernel.GTruth`.
  - Output: `Flow-continuity-K` (aliases: `scott-continuity-K`, `ω-continuity-K`),
    `Th*-as-sup-K` (aliases: `kleene-approximation-K`, `kleene-fixedpoint-K`).

- Guarded code theorems — `LogOS/Theorems/Code/Core.agda`
  - Guard naturality (decode‑level): Requires a `KernelHom` h, `KernelHomFlow h` (Flow preservation on boundary), plus Kernel fields `guard-decode`, `body-decode`, and `KernelHom.map-decode`.
    - Output: `guard-naturality-decode`, packed in `GuardHom`.
  - Decode‑level equalities: Requires only Kernel fields (`reify-decode`, `body-decode`, `guard-decode`).
    - Output: `reify-decode-eq`, `body-decode-eq`, `decode-FlowCode-eq`.
  - Decode‑level monotonicity: Requires `BodyMonotone K`.
    - Output: `decode-FlowCode-mono` (alias: `flowcode-mono-decode`).

- Reflection congruences — `LogOS/Theorems/Boundary/Reflection.agda`
  - Requires: only the core Kernel fields (`decode∘encode`, `reify-decode`, `decode-γ*`).
  - Output: `reify-idempotent-decode`, `reify-retraction-decode`, plus boundary observational equivalence (`_≈∂_`).

- γ* preservation (decode‑level) — `LogOS/Theorems/Boundary/Guarded.agda`
  - Requires: `KernelHomFlow` (preserves‑Th via `FlowHom`), and Kernel fields `decode-γ*`, `KernelHom.map-decode`.
  - Output: `decode-mapCode-γ*≤Th*`.

- Spectral separation (finite convergence) — `LogOS/Theorems/Boundary/SpectralSeparation.agda`
  - Output: `finite-convergence-inequalities`, `finite-convergence-equalities`.

- Adapter surface — `LogOS/Adapters/All.agda`
  - Provides lean re-exports for adapter‑level reasoning; initial kernel adapters live in `LogOS/Kernel/Initial.agda`.

- S‑level entailment and cut — `LogOS/Theorems/SemanticCut.agda`
  - Requires: `Kernel.Strict` (`Sat_S`), S↔H coherence `Kernel.coh-LH : _↔_`, translation `Kernel.TransH`, and H‑layer monotonicity (`HomotypicalTruth.HLayer.mono-Con`).
  - Output: `reflS`, `cutS` (admissibility by composition), and `ineq→Ent_S` (boundary inequality implies S‑entailment).

Meta (Conditional) — `LogOS/Theorems/Meta/*`
- Assumptions: `LogOS/Theorems/Meta/Assumptions/Core.agda` includes `DecodeExtensional`, provability packs, and `BoundaryFix` (an explicit optional monotone fixed‑point principle).
  Diagonalisation/self-reference packs live in `LogOS/Theorems/Meta/Assumptions/Diagonal.agda`.
- Transport: `LogOS/Theorems/Meta/Full.agda` supplies the textbook transport lemma `noDecider-transport` (undecidability along the canonical fold), plus helpers like `decodeExt-pull`.
- Rice/Tarski: `LogOS/Theorems/Meta/Rice.agda`, `LogOS/Theorems/Meta/Tarski.agda` are transport wrappers: supply a local FreeKernel `¬ DeciderC` proof for the pulled‑back predicate.
- Löb/Gödel: `LogOS/Theorems/Meta/Lob.agda` defines `ProvabilityOps` and `LoebAxiom`; `LogOS/Theorems/Meta/Godel.agda` uses them to package Gödel‑2 conditional unprovability.
- Landauer (logical resource bound): `LogOS/Theorems/Meta/Landauer.agda` defines a small assumption pack
   with an energy carrier (`Scale`), a program `cost : Cosp → Scale`, a predicate `Merges`, and a
   distinguished lower‑bound unit `L`, yielding a Landauer‑style theorem `landauer : Merges f → L ≤ cost f`.
   A boundary‑I/O flavored variant `LogOS/Theorems/Meta/LandauerIO.agda` adds subadditivity for composition/tensor
   and an identity bound.
- Hilbert–Pólya flow: example‑level utilities live in `LogOS/Domain/Opacity/NumberTheory/HP/Flow.agda` to keep
  operator semantics out of the core. Given an `HPInterface` pack (operator `Op`, embedding `embed`,
  and intertwining `embed ∘ Flow ≡ Op ∘ embed`), it provides transport lemmas between fixed points
  of Flow and fixed points of `Op`; with a faithful embed, `Op`‑fixed implies a strong Flow fixed‑point.

Boundary Fixed Points (Non‑vacuous)
-----------------------------------
- BoundaryFix (assumption pack): `LogOS/Theorems/Meta/Assumptions/Core.agda`
  - `fixH : (f : Con∂ → Con∂) → Mono f → Σ Con∂ (λ c → c ⊑ f c × f c ⊑ c)` — a fixed point up to mutual refinement for every monotone endomap.
  - This is model‑local and not globally postulated; many developments instead assume a more concrete diagonalisation principle (e.g. `TruthDiagonal`) directly.
- Scott constructor (example‑ready): `LogOS/Theorems/BoundaryFixFromScott.agda`
  - `BoundaryFix‑from‑Scott K (λ f mono → ScottFix (bnd BB) f)` wraps a Scott fixed point (for monotone `f`) into `BoundaryFix`.
- Minimal instance: a one‑point boundary poset yields a concrete `BoundaryFix` with no postulates.

Projective Perspective (Fixed‑Point Logic)
-----------------------------------------
- Projectors: A `Projector` on a constraint poset `CP` consists of an inflationary,
  idempotent‑lax endomap `P : Con → Con` with `infl : c ⊑ P c` and `idemp‑lax : P (P c) ⊑ P c`.
- Fixed‑points: `Projective.fixedPoints` packages the poset of fixed points as pairs
  `(c , P c ⊑ c × c ⊑ P c)` ordered by the ambient `⊑`. This supports “projective” reasoning:
  truths stable under a chosen closure form a sub‑poset.
- Instances in LogOS:
  - Guarded closure (G‑tier): the global step `Flow` acts as a projector
    (`Projective.ForG.fromGuarded`). Its fixed points are the globally stable truths.
  - H‑tier invariance on the boundary poset: `Inv_H` is a projector
    (`Projective.ForH.fromInvariance`), capturing invariants as fixed points.

Local vs Global Truth — Fixed‑Point Strengthening (with ω‑sups)
--------------------------------------------------------------
- In preorder form, the guarded fixed‑point laws are given as inequalities
  (`Th*‑fixed : Th* ⊑ Flow Th* × Flow Th* ⊑ Th*`). This is intentional: the core only
  assumes preorders, not antisymmetry.
- When a model supplies ω‑completeness and continuity (via `GuardedTruth.OmegaCPO`
  and `GuardedTruth.FiniteFirst.cont‑ω`), μ‑induction and continuity theorems hold
  (`LogOS.Theorems.Boundary.Mu`, `LogOS.Theorems.Boundary.Continuity`). If in addition the boundary
  preorder is upgraded to a partial order (antisymmetry), these inequalities identify
  a genuine least fixed point.
- Optional ω‑sup selection: models supply ω‑chain suprema explicitly via `LogOS.Axioms.OmegaSup.Interface` and `omegaCPO-from-chainSup`.
  This strengthens the “local truth as iterative approximants” view into “local truth
  equals global truth (least fixed point)”, provided the ambient order is a partial order.
  The ω‑sup selection sits entirely in the model boundary; the proven Minimal/Kernel core remains `--safe`.

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
- Helpers (continuity): `LogOS/Helpers/ContinuityOne.agda`

Optional: Opacity (and GRH as Application)
-----------------------------------------
The Opacity strand lives outside the Minimal/Kernel core and is expressed via small,
opt‑in packs. It provides conditional transport and barrier theorems once you supply
explicit bridges.

- Spectral adapter (ζ facts): `LogOS/Domain/Opacity/NumberTheory/LFunction/RiemannFacts.agda`
  - `RiemannSpectralFromFacts` sets `OnLine s` to `Re s ≡ 1/2` and isolates ξ‑zeros.

- Finite bridge (operator path; application): `LogOS/Domain/Opacity/Applications/GRH/ZetaBridge.agda`
  - `ZetaOpBridgeFinite` (two fields: zero→OpFixed, OpFixed→OnLine) and
    `GRH_Without_Vacuity_Guards_from_finite` (derives `∀ s, NontrivialZero s → OnLine s`).
  - Convenience: diagonal adapter `LogOS/Domain/Opacity/Applications/GRH/DiagonalToHPBridge.agda` and
    wrapper `LogOS/Domain/Opacity/Applications/GRH/DiagonalAdapter.agda`.

- Limit wrapper (continuity/ω‑sups; application): `LogOS/Domain/Opacity/Applications/GRH/HPGRHLimit.agda` (and ω‑sup variants)
  - `ZetaOpBridgeLimit` for finite witnesses + limit clause; ω‑sup selection builds `OmegaCPO`.
  - Concrete modules: `LogOS/Domain/Opacity/Applications/GRH/HPGRHLimit.agda`, `LogOS/Domain/Opacity/Applications/GRH/HPGRHLimitOmegaSup.agda`.

- Weil positivity (explicit-formula style, schematic; opacity core): `LogOS/Domain/Opacity/WeilPositivityBridge.agda`
  - `WeilPositivityAssumptions` isolates the “positivity on all tests” axiom and the
    ζ-specific implication `probe-pos→OnLine`.
  - `WeilPositivityObservable` is the observer-facing refinement: positivity is only
    required on a designated `Observable` class of tests, and each nontrivial zero must
    produce an observable probe. `GRH_Without_Vacuity_Guards_from_WeilPositivityObservable` then derives
    `GRH_Without_Vacuity_Guards`.

- Categorical (nucleus) bridge: `LogOS/Theorems/Meta/GRHBridge.agda`
  - `GlobalNucleusBridge`: projector (closure) on boundary truth + selector; zeros
    yield closed witnesses and “closed ⇒ OnLine”. See `LogOS/Domain/Opacity/LogicLanglands.agda` and
    `LogOS/Domain/Opacity/Applications/GRH/Systems.agda` for concrete instantiations alongside the operator route.

Opacity / GRH Bundle Map (Optional, Isolated)
---------------------------------------------
- Opacity core (ledgers, observability, limit/cofinal infrastructure): `LogOS/Domain/Opacity/*`.
- GRH application wrappers (operator and diagonal routes): `LogOS/Domain/Opacity/Applications/GRH/*`.
- Categorical path (operator‑free): use `LogOS/Theorems/Meta/GRHBridge.agda` plus
  `LogOS/Domain/Opacity/LogicLanglands.agda`, which records the nucleus/projector bridge alongside a
  spectral adapter. This keeps the application story decoupled from operators when desired.

Architecture Notes (Opacity Isolation)
--------------------------------------
- Core remains `--safe` and free of analytic/operator imports. Only closure/fixed‑point
  abstractions live in core (Flow and Projector/Nucleus).
- All GRH‑specific code (operators, finite regulators) sits under `LogOS/Domain/Opacity/Applications/GRH/*`.
- The categorical bridge stays operator‑free, phrased over a generic `SpectralPack`.
- Prefer adapters that accept `SpectralPack`; avoid depending on `RiemannSpectral` unless
  needed for classical alignment. `LogOS/Domain/Opacity/SpectralFromFacts.agda` provides a clean path.

Scope: these are conditional wrappers; no new analytic content is proved. The Minimal/Kernel
core remains `--safe`.

GRH with vacuity guards
--------------------------------------
To make the RH/GRH statement non-vacuous as a claim object, the production library includes:

- Guards for a spectral adapter (nontrivial zeros exist; `OnLine` is not tautological):
  - `LogOS/Domain/Opacity/Meaningfulness.agda`
- Packaged GRH claim surface with guards (bundle guards + GRH proof):
  - Canonical surface: `LogOS/Domain/Opacity/GRH.agda`
    (re-exports `LogOS/Domain/Opacity/GRH_Vacuity_Guards.agda`).
- Raw predicate alias (no guards): `GRH_Without_Vacuity_Guards` (from `ZerosPack.GRH_Without_Vacuity_Guards`).

Theorem ↔ Axioms ↔ Paths
------------------------
| Theorem(s) | Required fields (records) | Source path(s) |
|---|---|---|
| `LogOS.Theorems.Laws.FiniteKernel.S.S→H`, `H→S` | `Kernel.coh-LH : _↔_`, `Kernel.Strict`, `Kernel.TransH` | `LogOS/Theorems/Laws/FiniteKernel/S.agda`, `LogOS/Kernel.agda` |
| `LogOS.Theorems.Laws.FiniteKernel.H.fold∂-preserves`, `foldb-preserves` | `interp∂-mono`, `interpb-mono` (from free algebra fold) | `LogOS/Theorems/Laws/FiniteKernel/H.agda`, `LogOS/Free/Constraints.agda` |
| `LogOS.Theorems.Laws.FiniteKernel.H.complete∂`, `completeb` | `FreeConAlg`, `idHom≡` (choose identity on Free) | `LogOS/Theorems/Laws/FiniteKernel/H.agda`, `LogOS/Free/Constraints.agda` |
| `LogOS.Theorems.Boundary.Mu.μ-unfold-left`, `μ-unfold-right` | `GuardedTruth.GuardedClosure.Th*-fixed` via `Kernel.GTruth` | `LogOS/Theorems/Boundary/Mu.agda`, `LogOS/Minimal/Truth.agda`, `LogOS/Kernel.agda` |
| `LogOS.Theorems.Boundary.Mu.μ-induction-K` | `GuardedTruth.OmegaCPO`, `GuardedTruth.FiniteFirst` at `BulkBoundary.bnd (Kernel.BB K)` | `LogOS/Theorems/Boundary/Mu.agda`, `LogOS/Minimal/Truth.agda` |
| `LogOS.Theorems.Boundary.Continuity.Flow-continuity-K` | `GuardedTruth.OmegaCPO`, `GuardedTruth.FiniteFirst` | `LogOS/Theorems/Boundary/Continuity.agda`, `LogOS/Minimal/Truth.agda` |
| `LogOS.Theorems.Boundary.Continuity.Th*-as-sup-K` | `GuardedTruth.FiniteFirst.Th⋆-as-sup` | `LogOS/Theorems/Boundary/Continuity.agda`, `LogOS/Minimal/Truth.agda` |
| `LogOS.Theorems.Code.Core.guard-naturality-decode`, `GuardHom` | `KernelHom` + `KernelHomFlow` (Flow hom), `Kernel.guard-decode`, `Kernel.body-decode`, `KernelHom.map-decode` | `LogOS/Theorems/Code/Core.agda`, `LogOS/Kernel/Hom.agda`, `LogOS/Kernel.agda`, `LogOS/Minimal/Truth.agda` |
| `LogOS.Theorems.Code.Core.reify-decode-eq`, `body-decode-eq`, `decode-FlowCode-eq` | `Kernel.reify-decode`, `Kernel.body-decode`, `Kernel.guard-decode` | `LogOS/Theorems/Code/Core.agda`, `LogOS/Kernel.agda`, `LogOS/Minimal/Truth.agda` |
| `LogOS.Theorems.Boundary.Guarded.decode-mapCode-γ*≤Th*` | `KernelHomFlow.preserves-Th`, `Kernel.decode-γ*`, `KernelHom.map-decode` | `LogOS/Theorems/Boundary/Guarded.agda`, `LogOS/Kernel/Hom.agda`, `LogOS/Kernel.agda` |
| `LogOS.Theorems.Boundary.SpectralSeparation.spectral-separation-inequalities`, `spectral-separation-equalities` | `GuardedTruth.FiniteFirst` + `OmegaCPO` + `SpectralSeparationSpec`; optional `BulkBoundaryPO` (antisymmetry) for equalities | `LogOS/Theorems/Boundary/SpectralSeparation.agda` |
| Adapter helpers (general) | — (see initial kernel builders) | `LogOS/Theorems/Laws/FiniteKernel/Adapters.agda`, `LogOS/Kernel/Initial.agda` |

Optional: P vs NP (Conditional)
-------------------------------
The complexity story mirrors the GRH organization and stays outside the core. We use
graded-kernel flow on boundary constraints plus explicit “poly by size” predicates to
state P/NP-shaped interfaces, then isolate separation as a conditional pack of assumptions.

> **What this is / isn't**
> - **Not** a ZFC proof of classical P≠NP.
> - **Conditional:** if the stated assumptions hold in a model, the separation claim follows.
> - **Generic route:** the graded-flow interface (`DetPolyTimeBoundedG` / `PolyWitnessedTotalVerificationG`) is P/NP-shaped, not language-relative NP.
> - **Classical alignment is explicit:** only via `TruthRoute` + `ClassicalPvsNP`.
> **Reviewer quick-check**
> - Hardness is an explicit axiom (`InfoHardness` or `ProofLowerBound`), not derived.
> - The generic route is not classical NP; the classical surface is separate.

- Model (industry-aligned): `LogOS/Domain/Complexity/Model.agda`
  - `StandardCM`: wraps a generic `ComplexityModel` with a verifier pair encoding
    `encVW : (x , w) → ToyUCode` and a witness size `wsize` (useful when instantiating
    the kernel route with a concrete computation model).

- P/NP by grade polynomials (minimal graded route): `LogOS/Domain/Complexity/TruthRoute_Grade_Only.agda`
  (alias: `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda`)
  - `DetPolyTimeBoundedG`: ∃ grade polynomial `g` such that `Flow (g (size x)) (decode (DetRun x))`
    satisfies the chosen acceptance predicate for all `x`.
  - `PolyWitnessedTotalVerificationG`: ∃ grade polynomial `g` such that for each `x` there is a witness `w` with
    acceptance after `Flow` at grade `g (size x)` (no witness-size bound at this minimal layer).
  - `SuperPolyHardnessG`: ∀ grade polynomial `g`, ∃ `x` with ¬ `DetWithinAt (g (size x))` (graded closure failure).
  - `SpectralSeparationAssumptionsG`: `NP-witnessG : PolyWitnessedTotalVerificationG` and `Det-superpolyG : SuperPolyHardnessG`.
  - `PvsNPClaimG`: records `NP-holdsG` and `notP`; `mkPvsNPG` derives the claim from assumptions.

- NP with explicit witness-size bounds (within `TruthRoute`):
  - `TruthRoute.For.WithWitnessSize` (adds explicit witness-size bounds to the verifier interface).

- Correctness-carrying interface (within `TruthRoute`):
  - `TruthRoute.For.InP` / `TruthRoute.For.WithWitnessSize.InNP` (language-relative, correctness carried explicitly).

- “Strong-by-default” packaged claim surface (recommended for publication statements):
  - `LogOS/Domain/Complexity/PvsNP.agda`
  - Packaging only: the `Assumptions` already contain `InNP` and `¬ InP`.

- Classical interface (literature-aligned, ℕ-bound compat; cost = time): `LogOS/Domain/Complexity/ClassicalPvsNP.agda`
  - Thin renaming of the grade-native physical classes specialized to ℕ-costs:
    `PhysicsClassesWGraded`/`PhysicsClassesWCostGuardsGraded`.
  - `FromTruthRoute` reinterprets `TruthRoute.For.InP` / `TruthRoute.For.WithWitnessSize.InNP` as classical `InP` / `InNP`
    once the polynomial predicate is aligned.

- Optional non-degeneracy laws (prevent vacuous models): `LogOS/Domain/Complexity/StandardCMLaws.agda`
  - `EncodingsInDomain`: encodings land in Blum halting domains (blocks “TimeLe always false / Domain empty”).
  - `ReasonableSize`: size is polynomially related to an explicit encoding-length measure.

Assumption ledger (one screen)
------------------------------

| Claim | Depends on | Where used |
|---|---|---|
| `PvsNPClaimG` | `Assumptions` (NP witness + bottleneck + hardness) | `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` |
| `Claim` (packaging only) | `InNP` + `¬ InP` (TruthRoute) | `LogOS/Domain/Complexity/PvsNP.agda` |
| `Claim` | `PhysNPwCostGuards` + `MergeMeasure` + `ProofLowerBound` | `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda` |

- Spectral separation pack (single entry): `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda`
  - `SpectralSeparationAssumptionsG`: instantiate directly with the generic NP verifier bounds and deterministic super-poly hardness.
  - `PvsNPPackG`: conditional separation derived from the pack; suitable for both operator and nucleus inputs.
  - Internal/compatibility: use `PvsNPFromInfo_Grade_Only` for the canonical route in the curated API.

- Recommended stable import surface: `LogOS/Models/Complexity/Core.agda`
  - Includes ProofSearch + the PvsNP interface and the minimal info-hardness route.
  - The P vs NP surface is available as `LogOS.Models.Complexity.Core.PvsNP`.
  - The classical P vs NP surface is available as `LogOS.Models.Complexity.Core.ClassicalPvsNP`.
- Safe P/NP-only surface: `LogOS/Models/Complexity/PvsNP/Public.agda`
- The minimal info-theory route is available as `LogOS.Models.Complexity.Core.PvsNPFromInfo_Grade_Only`
  (ℕ-bound adapter: `PvsNPFromInfo_Grade_Only.FromNat`).

Further reading: `docs/Application_PvsNP.lagda.md` (physics-aligned sufficient conditions for separation)
and `docs/Complexity.lagda.md` (verification vs search boundary).
Golden-path scaffold: `LogOS/Domain/Complexity/Examples/GoldenPath.agda`.

LogOS-native refinements (still conditional)
--------------------------------------------
The “native” route avoids committing to Turing-machine internals early. It phrases complexity
as resource interfaces over the kernel’s endo-DSL (graph rewriting), and keeps reversible/unitary
computation alive by charging only *irreversible* events (merges/measurements).

- Proof-theory interface (Cook–Reckhow): `LogOS/Domain/Complexity/CookReckhow.agda`
  - Used by the proof-search boundary (`LogOS/Domain/Complexity/ProofSearchBoundary.agda`) to make “verification vs bounded search” precise.

- Physical route (Landauer / merges): `LogOS/Domain/Universality/LCUToLandauer.agda`, `LogOS/Domain/Universality/SecondLaw.agda`
  - Grade-native pipeline: `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda`
  - Kernel route (TruthRoute-based): `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuardsGraded.agda` (module Kernel)
  - ℕ wrapper (compat): `LogOS/Domain/Complexity/PhysSeparationPipelineWCostGuards.agda`
  - Pipeline `PhysNP + MergeMeasure + ProofLowerBound → PhysNP × ¬ PhysP`.
  - Bridge to classical P/NP: `LogOS/Domain/Complexity/PhysToTruthRouteBridge.agda` (cost := time), so physical ¬`PhysP` implies ¬`InP`.
  - SAT target (nontrivial verifier cost): `LogOS/Domain/Complexity/Targets/SATPhysicalSeparationCostGuards.agda` (kernel route in `.Kernel`)

- Quantum/info route (measurements): `LogOS/Domain/Universality/MeasurementCapacity.agda`,
  `LogOS/Domain/Complexity/ResourceSchemaG.agda` (grade-native) with ℕ wrapper (compat) `LogOS/Domain/Complexity/ResourceSchema.agda`
  - Separates “poly-time with poly measurements” from languages whose classical information need cannot fit through the measurement/time budget.

- Info-hardness bridge (minimal axioms):
  - `LogOS/Domain/Complexity/InfoHardnessBridge.agda` (`DetBottleneck`, `InfoHardness`)
  - LOB adapters (grade-native): `LogOS/Domain/Complexity/InfoBottleneckAdaptersG.agda`
    (graded wrappers live in `InfoBottleneckAdaptersGraded`)
  - Convenience pack: `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` (`Assumptions`, `mkPack`)

- Shared resource schema:
  - Grade-native core: `LogOS/Domain/Complexity/ResourceSchemaG.agda`
  - GradeBound + ℕ-polynomial wrapper: `LogOS/Domain/Complexity/ResourceSchemaGraded.agda`
  - ℕ wrapper (compat): `LogOS/Domain/Complexity/ResourceSchema.agda`
  - Canonical backbone for time+non-unitary-event budgets (measurement-capacity route and proof-search pivot).

- Proof search boundary: `LogOS/Domain/Complexity/ProofSearchBoundary.agda`
  - Makes the verification vs bounded-search vs unbounded-search (“infinite resource limit” = Σℕ) boundary explicit.

- Proof search capstone:
  - Grade-native core: `LogOS/Domain/Complexity/ProofSearchCapstoneGraded.agda`
  - ℕ wrapper (compat): `LogOS/Domain/Complexity/ProofSearchCapstone.agda`
  - DetWithin route (kernel-friendly abstraction): `ProofSearchCapstoneGraded.DetWithinRoute`
  - Packages the “cofinal limit = provability” lemma and shows how a single resource-hardness premise blocks poly-budget deciders for provability (and hence for `P` via completeness transport).

- Local observability budget (LOB):
  - Grade-native core: `LogOS/Domain/Complexity/ObservabilityBudgetG.agda`
  - GradeBound + ℕ-polynomial wrapper: `LogOS/Domain/Complexity/ObservabilityBudgetGraded.agda`
  - ℕ wrapper (compat): `LogOS/Domain/Complexity/ObservabilityBudget.agda`
  - Factors the “global non-unitary operations” story into a single pack that produces `ResourceSchema.Capacity` + `ResourceSchema.Throughput` (so domains don’t have to wire those separately).

- StableP reflection barrier: `LogOS/Domain/Complexity/Targets/StablePProofSearchReflectionBarrier.agda`
  - For `P = LogOS.Theorems.Meta.Flow.StableP K`, any complete proof system has an unbounded provability predicate whose decidability would decide stability; the existing meta-theorem pipeline blocks this (Gödel/diagonal flavor, but LogOS-native).

- Data Processing Inequality (DPI): `LogOS/Domain/Universality/DataProcessingInequality.agda`
  - A minimal interface stating that admissible post-processing cannot increase classical information; useful to phrase “learning requires global operations” as an explicit information-need premise.

- Non-unitary capacity pivot: `LogOS/Domain/Universality/NonUnitaryCapacity.agda`
  - Unifies “measurement” and “forgetting/abstraction” as counted non-unitary events with an information-per-event capacity bound; lets domains state softer global-nonunitarity assumptions while reusing the same separation bridges.

Notes
- As with GRH, the logic proves no analytic/combinatorial facts about complexity in the core.
  All assumptions are explicit and live in `LogOS/Domain/Complexity/*`.
  This keeps the Minimal/Kernel `--safe` and reusable.
ZF in the Limit (Cumulative Hierarchy)
--------------------------------------
- Flow surface: `LogOS/Domain/SetTheory/Dsl.agda` packages any `ZFAxioms` instance with a boundary interpretation (`realise`) and guarantees that membership/equality respect the canonical global step `Flow`. Downstream models instantiate the DSL first, then call `surfaceToZFAxioms` to retrieve the classical pack with boundary guarantees in tow.
- Interface: `LogOS/Domain/SetTheory/LimitPack.agda` defines `CumulativeHierarchy K` (colimit universe) and `toZFAxioms` (adapter to `ZFAxioms`).
- Packs for stages: `LogOS/Domain/SetTheory/Cumulative.agda` declares the stage‑level packs (`StageIndex`, `StageSet`, `SuccessorClosure`, `LimitClosure`, `RankBounding`, `DecodeBridge`) and bundles them in `StageToCH` with a provided `CumulativeHierarchy`, plus the boundary realisation witnesses required by the Flow surface (`realise∞`, `mem⇒flow∞`, `eq⇒realise∞≡`, `tf-stable∞`). `StageIndex` records comparability data (a canonical base successor `zeroStage`, a “join” operation, and `succAbove`) so transfinite towers can be glued into a single hierarchy; `StageSet` is universe-polymorphic and exposes stage‑local extensionality/equality fields so global proofs can be lifted.
- Stage-to-DSL adapter: `LogOS/Domain/SetTheory/CumulativeSurface.agda` defines `stageToSurface`, consuming any such `StageToCH` bundle and producing a `ZFDsl` witness. A minimal, LogOS-native adapter `LogOS/Domain/SetTheory/StageToCHFromHierarchy.agda` turns any already-built `CumulativeHierarchy K` into a `StageToCH K` (constant stages, canonical `Th⋆` realisation). `LogOS/Domain/SetTheory/FromZFAxioms.agda` provides the parallel adapter `ZFAxioms K → CumulativeHierarchy K`.
- WF-graph route (core): `LogOS/Domain/ZFC/WFGraph/Model.agda` + `LogOS/Domain/ZFC/WFGraph/ZFC.agda` implement “sets as well-founded membership graphs”, producing definable-ZF(+Infinity) and (optionally) full `ZFAxioms`. `LogOS/Domain/ZFC/WFGraph/Surface.agda` is the one-stop façade: `Definable` exposes the definable pack, and `Full` exposes `zf`, `CH`, `stageToCH`, and `surface`. ZFC is obtained by adding an explicit AC witness (`LogOS/Domain/SetTheory/ChoiceAxiom.agda`) to `ZFCAxioms` (`LogOS/Domain/SetTheory/Pack.agda`).
- Derived set constructors: `LogOS/Domain/SetTheory/Derived.agda` collects small “derived” operations (like `singleton` and binary union) over any `ZFAxioms` instance to keep downstream developments lean.
- Membership graphs (supplementary): `Data/Graph.agda` defines the canonical graph datatype (vertex carrier + adjacency relation). `LogOS/Domain/ZFC/Supplementary/HF/HFGraph.agda` interprets the HF universe through that graph lens (vertices = HF sets, edges = membership). This is useful for rewriting-style experiments but is not on the core WF-graph mechanisation path.
- Algebraic graphs: `LogOS/Algebra/GraphSurface.agda` lets any `FiniteGraph` (adjacency matrix over a ring) supply a pure adjacency predicate and immediately exposes it as a `Data.Graph`. This is the natural bridge for Ihara/GRH packs so they can share the same graph semantics as the HF/cumulative hierarchy side without duplicating definitions.
- Ordinal scaffold: `LogOS/Domain/ZFC/OrdinalScaffold.agda` provides the ordinal-based `StageIndex` (with joins/successor witnesses) plus a record of assumptions (`OrdinalStageCommon`, `OrdinalHierarchy`) that capture the remaining work *for the ordinal-based cumulative hierarchy route*: stage sets, successor/limit closures, rank-bounding, and the final cumulative hierarchy with Flow realisation. Supplying that record yields a `StageToCH K` and a `ZFDsl K` via `OrdinalSurface`. (The core WF-graph route already provides an end-to-end ZF(+Infinity) interpretation; AC remains an explicit add-on.)
- Flow closure: `LogOS/Domain/ZFC/ClosureEndo.agda` provides the *generic* closure-step API (compose ZF-like constructor steps as `id ≤ Step ≤ Flow-Endo`). `LogOS/Domain/ZFC/ClosureModel.agda` is the corresponding scaffold for building a fixed point (`Th⋆`) from approximants and repackaging it as a `CumulativeHierarchy`/`ZFDsl`. HF-based components live under `LogOS/Domain/ZFC/Supplementary/HF/*`.
- No hidden assumptions: construct `CH` from explicit packs (successor/limit closure; Scott continuity + ω‑sup selection on boundary posets; rank bounding for Separation/Replacement). Then use `toZFAxioms` to expose a full ZF interpretation (and optionally add set‑theoretic AC separately). This mirrors the standard cumulative hierarchy argument and leverages the logic’s fixed‑point continuity infrastructure.
