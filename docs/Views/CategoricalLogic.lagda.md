<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Categorical Logic (Computational Trinity)

```agda
{-# OPTIONS --safe #-}
module docs.Views.CategoricalLogic where

-- Typechecked “view surface” for the categorical-logic presentation.
--
-- Keep this module intentionally lightweight: it should be importable alongside
-- other views/tests without introducing operator/name clashes.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheorems

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = ViewTheorems.For K
  open V.CategoricalLogic public

  private
    CodeThinCat-exists : _
    CodeThinCat-exists = CodeThinCat

    BoxFunctor-exists : _
    BoxFunctor-exists = BoxFunctor

    Kernel2Cat-exists : _
    Kernel2Cat-exists = Kernel2Cat

    Port2Cat-exists : _
    Port2Cat-exists = Port2Cat

    KernelCategory-exists : _
    KernelCategory-exists = KernelCategory

    quantale-exists : _
    quantale-exists = quantale

    conAlg-exists : _
    conAlg-exists = conAlg

    projection-exists : _
    projection-exists = V.Projections.projection
```

This note states the **categorical-logic leg** of the “computational trinity”
for the production LogOS library. The guiding principle is: we keep category
theory *out of the core signature*, but the core structures already *are*
categorical once you look at them through the right lens.

Interpretation (analogy):
this document is a derived presentation (“view”) over the same kernel interfaces;
it does not add logical power.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.

Scope (formal)
--------------
- Parameter: `Kernel Sig Q`.
- Surface: `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CategoricalLogic`).

Adapter mapping to the literature (quick table)
-----------------------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Preorder as a thin category | `ConPreorder` (`LogOS/Minimal/Con.agda`) | “Category laws” are ops-level unless you assume proof-irrelevance. |
| Monoidal structure on a preorder (ops vs laws) | `MonoidalOps` / `MonoidalLaws` (`LogOS/Minimal/Adjunction.agda`) | Ops are always available; laws are opt-in. |
| (Lax) adjunction / Galois connection | `LaxAdjunction`, `GaloisConnection` (`LogOS/Minimal/Adjunction.agda`) | Kernel uses the lax (inequality) form by default. |
| Frobenius reciprocity (lax) | `Frobenius.frobenius-ext≤` (`LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda`) | One-way inequality; avoids collapsing irreversible structure. |
| Beck–Chevalley (lax) | `LogOS/Theorems/CategoryTheory/BeckChevalley.agda` | Presented as commutation squares up to refinement. |
| Kernel morphisms as 1-cells, refinement as 2-cells | `LogOS/Kernel/Hom2Cat.agda`, `LogOS/Kernel/Graded/Hom2Cat.agda`, `LogOS/Kernel/LogicKernel/Hom2Cat.agda`, `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda` | Locally preordered 2-category interface. |
| Ports/adapters as a 2-category | `LogOS/Theorems/CategoryTheory/Port2Cat.agda` | “Presentation independence” is expressed as 2-cells (`↔`-equivalences). |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital quantale in the finite-join sense (not complete) + time map. |

Assumptions (explicit)
----------------------
- **Proof-irrelevance** (or truncation) is needed if you want to treat refinement proofs as equalities of morphisms (literal thin categories).
- **Antisymmetry** is needed if you want to upgrade mutual refinement `c ⊑ d × d ⊑ c` to propositional equality `c ≡ d` (partial order reading).
- **Monoidal laws** are not assumed by default: if you want textbook monoidal categories, add `MonoidalLaws`/`Monoidal`.

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: preorder-as-thin-category structure, monoidal/adjunction patterns, and coherence theorems (Frobenius/Beck–Chevalley).
- Weaker/lax by default: 2-cells are refinement witnesses (directed/irreversible), and “laws” are ops-level unless you assume proof-irrelevance/antisymmetry.
- Added by ports/adapters: “presentation independence” is expressed as port-level translation/naturality rather than as a single privileged syntax.
- Assumption-scoped: any equality-level categorical structure is an explicit upgrade (e.g. `MonoidalLaws`, antisymmetry/proof-irrelevance packs).

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CategoricalLogic`):
  `CodeThinCat`, `BoxFunctor`, `Kernel2Cat`, `Port2Cat`, `KernelCategory`, `quantale`, `conAlg`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- The prose below is explanatory; the statements above are the authoritative claims.

Preorder-category operations from refinement
-------------------------------------------

Every `ConPreorder` admits a preorder-category **operations** view:

- objects: constraints `Con`
- morphisms: refinement proofs `c ⊑ d`
- identity: `refl`
- composition: `trans`

The production library exposes this as the primitive notion of “reasoning step”:
all computational/semantic structure is phrased over refinement rather than
judgmental equality.

**Note (no proof-irrelevance assumed).** In Agda, a refinement proof `c ⊑ d` is a
term of a type, and the library does not assume those proof types are
subsingletons. So by default we treat this as an **ops-only** categorical façade:
we use only the preorder laws (`refl`, `trans`) and avoid stating category laws
as equalities of proofs. If you add proof-irrelevance (or work in a truncated
setting), the usual thin-category reading (and equality-level laws) becomes
literal.

Monoidal ops and lax adjunction (categorical logic)
---------------------------------------------------

The categorical logic structure that LogOS actually needs is:

1. monoidal-*ops* on constraints (tensor/unit operations + monotonicity) for “tensor/overlay” reasoning, and
2. a lax adjunction between bulk and boundary constraints (for open-system I/O).

These are packaged in the Minimal layer:

- `LogOS/Minimal/Adjunction.agda`
  - `MonoidalOps` (tensor/unit operations + monotonicity; laws are optional via `MonoidalLaws`)
  - `Monoidal` (ops + laws bundle, when you want a real monoid up to `≈`)
  - `LaxAdjunction` (lax unit/counit inequalities; the ↔-law “tight” form is `GaloisConnection`)
  - `LaxAdjunctionMono` (monotone lax adjunction; derives a `GaloisConnection`)
  - `LaxMonoidalAdjunction` (monoidal compatibility)
- `LogOS/Minimal/WorldLaws.agda` (`CtxPreorder`): optional preorder laws for the context relation `_≤ctx_`.

At the Kernel level, the corresponding bundled interface is:

- `LogOS/Algebra/ConAlg.agda` (`ConAlg`)

which exposes:

- a `BulkBoundary` of preorders (posets if antisymmetry is supplied),
- monoidal-*ops* on bulk and boundary, and
- a lax monoidal adjunction `ext ⊣ bnd` (in the unit/counit-inequality sense).

Cheap coherence (lax Beck–Chevalley / Frobenius)
-----------------------------------------------

Without importing full Lawvere semantics, LogOS still supports some “hyperdoctrine-shaped”
coherence at the preorder (`_⊑_`) level:

- **Frobenius (one-way)** from the lax monoidal adjunction axioms:
  `LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda` (`Frobenius.frobenius-ext≤`).
- **Boundary closure** induced by the adjunction, once monotonicity is supplied:
  `T = bnd ∘ ext` as a `ClosureOp` via `LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda`
  (`Derived.T-closureOp`).
- **Beck–Chevalley (lax)** as commutation squares up to refinement:
  `LogOS/Theorems/CategoryTheory/BeckChevalley.agda`.

Quantale enrichment (resource-aware categories)
----------------------------------------------

The quantitative adapter `QAdapter` is a **unital quantale in the finite-join sense** (not complete): `Scale` is a preorder with a
binary join (`_⊔s_`) and bottom (`⊥s`), and a monoid multiplication (`_·_`, `e`) distributing over join, with a
time monoid homomorphism `τ : Time → Scale`. This supplies the generic “budget algebra” used across
universality, complexity, and opacity.

Categorically:
- `WorldH` equips strict worlds with a `WFlow : WorldS → WorldS → Scale` satisfying the identity and composition
  inequalities (`e ≤ WFlow w w` and `WFlow w w' · WFlow w' w'' ≤ WFlow w w''`),
  i.e. a category enriched over the **monoidal preorder** underlying `Scale` (using `_·_`, `e`, and `_≤s_`).
  The Kripke-style context relation `_≤ctx_` (often taken as a preorder) is used for satisfaction monotonicity.
  When you want the preorder reading, supply `CtxPreorder` from `LogOS/Minimal/WorldLaws.agda`.
- In graded kernels (`LogOS/Kernel/Graded.agda`), the boundary flow is indexed by grades `g : Scale`,
  enabling resource-aware closure/normalisation arguments.

Category of kernels (morphisms up to decoded `≡`)
--------------------------------------------

For a fixed signature `Sig` and adapter `Q`, kernels form a category where the
notion of equality on morphisms is **strict propositional decode equality (`≡`)** (two morphisms are
identified if they induce the same decoded boundary constraint at the target).
Concretely, this is pointwise: `eqHom f g` iff `∀ γ → decode (mapCode f γ) ≡ decode (mapCode g γ)`.

The production library packages this as:

- `LogOS/Theorems/CategoryTheory/KernelCat.agda`
  - `KernelCat` (category structure)
  - `KernelCat-instance` (concrete instance with `KernelHom`)
  - `InitialUpToDecode` + `initial-from-build` (initiality of the FreeKernel, up to decode)

2-category of kernels (refinement as irreversible 2-cells)
----------------------------------------------------------

The more *primitive* structure in LogOS is preorder-enriched: morphisms are
compared by **refinement** rather than identified by equality.

- objects: kernels
- 1-cells: kernel morphisms equipped with boundary monotonicity
- 2-cells: pointwise refinement on decoded code maps at the target

This expresses **irreversibility** directly: 2-cells need not be invertible, and
composition respects refinement by whiskering (monotonicity).

This is a preorder-enriched (“locally preordered”) 2-category interface: 2-cells
are refinement witnesses, vertical composition is transitivity, and interchange
follows from whiskering monotonicity. If you additionally assume proof-irrelevance
for refinement proofs, this becomes literally thin/locally posetal.

In code:

- Core 2-cell operations (whiskering / horizontal composition):
  - `LogOS/Kernel/LogicKernel/Hom2Cat.agda` (primary, interface-level)
  - `LogOS/Kernel/Hom2Cat.agda`
  - `LogOS/Kernel/Graded/Hom2Cat.agda`
- Shared wrapper record shapes (used by all instances):
  - `LogOS/Theorems/CategoryTheory/WrapperCore.agda` (`Ref2Cat`, `HoCat`)
- Minimal preorder-enriched 2-category packaging (`Thin2Cat`) from preorders:
  - `LogOS/Minimal/Thin2Cat.agda`
- Packaged “2-category-like” interfaces (lightweight, no extra axioms; instances only):
  - `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda` (instantiates `Ref2Cat`)
  - `LogOS/Theorems/CategoryTheory/Kernel2CatGraded.agda` (instantiates `Ref2Cat`)
  - `LogOS/Theorems/CategoryTheory/Port2Cat.agda` (ports/adapters; satisfaction-equivalence as 2-cells)

The 1-category `KernelCat` is the decode-equality 1D façade: it identifies morphisms
by decoded propositional equality (`eqHom`). This is compatible with the refinement
2-category reading (both are phrased at decode level), but it is *not* implemented
as a quotient of the refinement preorder on 1-cells.

2-category of ports/adapters (boundary-level)
---------------------------------------------

The same 2-categorical language is available at the boundary:

- objects: boundary ports (presentations of a shared boundary satisfaction relation),
- 1-cells: port adapters (satisfaction-preserving translations),
- 2-cells: adapter equivalences (`Adapter≈`, pointwise satisfaction `↔`).

This packages the **ports/adapters calculus** as a native 2-category interface,
so boundary interoperability uses the same whiskering/vertical/horizontal
composition vocabulary as kernel refinement.

In code:

- `LogOS/Theorems/CategoryTheory/Port2Cat.agda` (`Port2Cat` + `Port2Cat-instance`)

```agda
module UsageSketch where
  open import LogOS.Prelude
  open import LogOS.Base.Signature using (LogOSSignature)
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.Minimal.World
  import LogOS.Theorems.CategoryTheory.KernelCat as KC

  KernelCategory
    : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    → KC.KernelCat Sig Q
  KernelCategory = KC.KernelCat-instance

  InitialKernelCategory
    : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
      (H : (let module W = Worlds Sig in W.WorldH Q))
    → KC.InitialUpToDecode Sig Q
  InitialKernelCategory = KC.initial-from-build
```

The snippet above is a typechecked usage sketch; the authoritative surfaces live
in the module paths cited above.

Yoneda-style transport (LogOS-native)
------------------------------------

Once equality of morphisms is taken “up to decode”, representability can be stated
and Yoneda-style transport principles in a form that matches LogOS’ reflection
layer. The incremental development lives in:

- `LogOS/Theorems/CategoryTheory/Yoneda.agda`

This is the categorical counterpart to the meta-theory transport pipeline:
initial object + morphisms up to decoded sameness (`_≃K_` / `_≈K_`) ⇒ principled transport of
structures along folds, without claiming more extensionality than the boundary
actually supports.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- Multi-institution (classic model theory): `docs/Views/MultiInstitution.lagda.md`
- CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`
- Topos-shaped nuclei/sheaves reading: `docs/Views/Topos.lagda.md`
