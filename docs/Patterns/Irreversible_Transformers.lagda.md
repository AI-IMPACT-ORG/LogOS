<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: irreversible transformers

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Irreversible_Transformers where

open import LogOS.API.LT
import LogOS.API.Ports.Physical
import LogOS.Apps.Irreversibility.All
```

This note records the post-refactor stance on irreversible processes.

The design choice is:

- `LOGᴳ` remains the strongest architectural ceiling: refinement may use the full boundary discipline.
- exported `LOG` remains the working thin 2-category, because whiskering/refinement stability still depends on implementation-aware morphism structure.
- the decoded-only boundary layer is useful as a theorem/view layer, but it is **not** itself a thin 2-category in v1.1.
- the Deutsch-style category remains the existing port stack over the shared distributed-semantics ledger:
  locality + causality + local reversibility.
- the default irreversibility-facing thermodynamic extension is therefore
  **causal + Landauer**, packaged reader-facing as
  `LogOS.API.Ports.PhysicalOptional.Landauer` and implemented by
  `LogOS.Ports.AbstractCausalLandauer2Cat`.
- the reversible Deutsch slice is a restriction theorem over the same ambient
  causal story, not a separate thermodynamic base.

## What is defined

The code now contains five separate but adjacent ingredients.

1. Generic reversibility obstruction:
   `LogOS.LT.ConPreorder.Isomorphism.orderIso-reflects-≈` and
   `LogOS.LT.ConPreorder.Isomorphism.collapse-obstructs-orderIso`.

2. Fibrewise physical corollaries:
   `LogOS.Ports.AbstractDeutsch2Cat.Reversibility.localReversible-reflects-≈` and
   `LogOS.Ports.AbstractDeutsch2Cat.Reversibility.collapse-obstructs-localReversible`.

3. General causal physical slice:
   `LogOS.Ports.AbstractCausal2Cat`.

4. Thermodynamic stack:
   reader-facing `LogOS.API.Ports.PhysicalOptional.Landauer`,
   implementation `LogOS.Ports.AbstractCausalLandauer2Cat`.

5. Optional opacity/factorisation pack:
   `LogOS.Ports.Opacity.Distinguishability`,
   `LogOS.Ports.Opacity.Obstruction`,
   `LogOS.Ports.Opacity.FiniteCompression`, and
   the downstream physical cost bridge `LogOS.Ports.AbstractLandauerObservational`.

Pedantic quantitative note:

- the bridge is now parameterised by a calibrated `CompressionValuation` into
  the ambient join-prequantale, not merely by an arbitrary monotone map out of
  `ℕ`,
- comparison of Landauer witnesses is exported as an explicit refinement
  preorder surface,
- unit-loss corollaries are phrased by refinement into actual cost, not by
  propositional equality of numerical representatives.

This means the irreversibility story is now:

- start with an ordinary causal physical map,
- show that it collapses distinguishable observations,
- conclude that no local reversibility witness can exist,
- layer cost separately with the Landauer port over the causal slice.

No negative “irreversible” port is introduced.

## What is *not* claimed

- `BoundaryDecode2Cat` is **not** promoted to the base category.
- the library does **not** identify irreversibility with partiality.
- the library does **not** derive the observational bridge from collapse alone;
  lower bounds on actual cost remain conditional on an explicit bridge record.
- the library does **not** define weighted or Shannon entropy in this change set.
- the library does **not** claim that every Landauer-decorated process is physically realistic.

The Turing-category bridge remains a forgetting comparison, not the native meaning of irreversible computation.

## Minimal example

`LogOS.Apps.Irreversibility.BitReset` gives the pure boundary-level example:

- a total reset map on a two-point boundary,
- collapse of `zero` and `one`,
- a proof that no order-isomorphism can realise that boundary action.

`LogOS.Apps.Irreversibility.BitResetDeutsch` gives the one-site physical comparison:

- the reset is a valid locality/causal morphism,
- it cannot lift to the Deutsch stack because that stack requires local reversibility.

`LogOS.Apps.Irreversibility.BitResetCompression` upgrades the same example to an
explicit finite-loss witness over a finite observed family.

`LogOS.Apps.Irreversibility.BitResetLandauer` then shows how a chosen bridge can
turn that finite-loss witness into a lower bound on actual Landauer cost, with
displayed `CostBound` statements recovered as corollaries.

The observation interface used there is intentionally narrow: it is now stated
for the chosen reset process itself, rather than as a global action on all
causal morphisms. That matches the mathematics actually needed by the example
and avoids advertising a stronger functoriality law than the current locality
layer provides.

`LogOS.Apps.Opacity.TagOpacity` shows that the same machinery also captures
hidden-tag opacity as compression from a finer private observation to a coarser
public one.

This is the intended architectural reading:
irreversibility is witnessed by **collapse of distinguishable observations**,
quantified first by pack-local finite-loss witnesses over explicit observed
families, while
thermodynamic cost is an explicit additional capability layer.
