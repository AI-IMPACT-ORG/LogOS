<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Categorical Logic — LogOS (Computational Trinity)

```agda
{-# OPTIONS --safe #-}
module docs.View_CategoricalLogic where

open import LogOS.Docs.Views.View_CategoricalLogic public
```

This note states the **categorical-logic leg** of the “computational trinity”
for the production LogOS library. The guiding principle is: we keep category
theory *out of the core signature*, but the core structures already *are*
categorical once you look at them through the right lens.

Thin categories from refinement
------------------------------

Every `ConPoset` can be read as a preorder-style category:

- objects: constraints `Con`
- morphisms: refinement proofs `c ⊑ d`
- identity: `refl`
- composition: `trans`

The production library exposes this as the primitive notion of “reasoning step”:
all computational/semantic structure is phrased over refinement rather than
judgmental equality.

**Note (no proof-irrelevance assumed).** In Agda, a refinement proof `c ⊑ d` is a
term of a type, and the library does not assume those proof types are
subsingletons. So we do not rely on “thinness” (at most one morphism between two
objects); we only use the preorder laws (`refl`, `trans`). If you add
proof-irrelevance (or work in a truncated setting), the usual “thin category”
reading becomes literal.

Monoidal structure and adjunction (categorical logic)
-----------------------------------------------------

The categorical logic structure that LogOS actually needs is:

1. a monoidal structure on constraints (for “tensor/overlay” reasoning), and
2. a lax adjunction between bulk and boundary constraints (for open-system I/O).

These are packaged in the Minimal layer:

- `LogOS/Minimal/Adjunction.agda`
  - `MonoidalPoset` (monoidal preorder-style category)
  - `LaxAdjunction` (bulk/boundary reflection interface)
  - `LaxMonoidalAdjunction` (monoidal compatibility)

At the Kernel level, the corresponding bundled interface is:

- `LogOS/Algebra/ConAlg.agda` (`ConAlg`)

which exposes:

- a `BulkBoundary` of preorders (posets if antisymmetry is supplied),
- monoidal structures on bulk and boundary, and
- a lax monoidal adjunction `ext ⊣ bnd`.

Quantale enrichment (resource-aware categories)
----------------------------------------------

The quantitative adapter `QAdapter` is a **finite‑join unital quantale** (`Scale`, i.e. a join‑semilattice
with bottom and a monoid multiplication distributing over join) with a
time monoid homomorphism `τ : Time → Scale`. This supplies the generic “budget algebra” used across
universality, complexity, and opacity.

Categorically:
- `WorldH` equips strict worlds with a `WFlow : WorldS → WorldS → Scale` satisfying lax unit/associativity,
  i.e. a category enriched over the **monoidal preorder** underlying `Scale` (using `_·_`, `e`, and `_≤s_`).
  The Kripke-style context order `_≤ctx_` is a separate preorder used for satisfaction monotonicity.
- The graded kernel (`LogOS/Kernel/Graded.agda`) indexes the boundary flow by grades `g : Scale`,
  enabling resource-aware closure/normalisation arguments.

Category of kernels (morphisms up to decode)
--------------------------------------------

For a fixed signature `Sig` and adapter `Q`, kernels form a category where the
notion of equality on morphisms is **decode-level equality** (two morphisms are
identified if they induce the same decoded boundary constraint at the target).
Concretely, this is pointwise: `f ≈ g` iff `∀ γ → decode (mapCode f γ) ≡ decode (mapCode g γ)`.

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

In code:

- Core 2-cell operations (whiskering / horizontal composition):
  - `LogOS/Kernel/LogicKernel/Hom2Cat.agda` (primary, interface-level)
  - `LogOS/Kernel/Hom2Cat.agda`
  - `LogOS/Kernel/Graded/Hom2Cat.agda`
- Shared wrapper record shapes (used by all instances):
  - `LogOS/Theorems/CategoryTheory/WrapperCore.agda` (`Ref2Cat`, `HoCat`)
- Packaged “2-category-like” interfaces (lightweight, no extra axioms; instances only):
  - `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda` (instantiates `Ref2Cat`)
  - `LogOS/Theorems/CategoryTheory/Kernel2CatGraded.agda` (instantiates `Ref2Cat`)

The 1-category `KernelCat` is the decode-level 1D façade: it identifies morphisms
by decode-level equality (`eqHom`). Conceptually, this *presents* the locally
posetal quotient of the refinement 2-category (it is not implemented as a
quotient type).

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
initial object + morphisms up to observational equality ⇒ principled transport of
structures along folds, without claiming more extensionality than the boundary
actually supports.
