<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Categorical Logic — LogOS (Computational Trinity)

```agda
module docs.View_CategoricalLogic where

open import LogOS.Docs.Views.View_CategoricalLogic public
```

This note states the **categorical-logic leg** of the “computational trinity”
for the production LogOS library. The guiding principle is: we keep category
theory *out of the core signature*, but the core structures already *are*
categorical once you look at them through the right lens.

Thin categories from refinement
------------------------------

Every `ConPoset` is a thin category:

- objects: constraints `Con`
- morphisms: refinement proofs `c ⊑ d`
- identity: `refl`
- composition: `trans`

The production library exposes this as the primitive notion of “reasoning step”:
all computational/semantic structure is phrased over refinement rather than
judgmental equality.

Monoidal structure and adjunction (categorical logic)
-----------------------------------------------------

The categorical logic structure that LogOS actually needs is:

1. a monoidal structure on constraints (for “tensor/overlay” reasoning), and
2. a lax adjunction between bulk and boundary constraints (for open-system I/O).

These are packaged in the Minimal layer:

- `LogOS/Minimal/Adjunction.agda`
  - `MonoidalPoset` (monoidal thin category)
  - `LaxAdjunction` (bulk/boundary reflection interface)
  - `LaxMonoidalAdjunction` (monoidal compatibility)

At the Kernel level, the corresponding bundled interface is:

- `LogOS/Algebra/ConAlg.agda` (`ConAlg`)

which exposes:

- a `BulkBoundary` of posets,
- monoidal structures on bulk and boundary, and
- a lax monoidal adjunction `ext ⊣ bnd`.

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

```text
open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World
open import LogOS.Theorems.CategoryTheory.KernelCat as KC

KernelCategory
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  → KC.KernelCat Sig Q
KernelCategory = KC.KernelCat-instance

InitialKernelCategory
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (H : (let module W = LogOS.Minimal.World.Worlds Sig in W.WorldH Q))
  → KC.InitialUpToDecode Sig Q
InitialKernelCategory = KC.initial-from-build
```

The snippet above is a *usage sketch* (kept in sync with the public API), not a
typechecked part of this document. For the authoritative typechecked surface,
follow the module paths cited above.

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
