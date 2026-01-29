<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Terminology — Literature ↔ LogOS (Canonical Meanings)

```agda
{-# OPTIONS --safe #-}
module docs.Terminology where

open import LogOS.Prelude public
```

This file fixes **canonical meanings** for specialised terms that appear across:
- `docs/Views/*` (semantic views),
- `docs/Applications/*` (packs),
- `docs/Paper/*` (paper).

The goal is not to impose one literature vocabulary, but to make the adapter
choices explicit and repeatable.

Quick conventions
-----------------
- **Judgmental equality** = Agda’s built-in conversion used by typechecking (not written as a symbol in the prose).
- **Propositional equality** = `_≡_` (proof-relevant).
- **Refinement** = preorder relation `_⊑_`.
- **Mutual refinement** = `≈` (two refinements).
- **Satisfaction equivalence** = `P ↔ Q` (paired implications).
- **Observational equality** = a satisfaction-induced equality/equivalence relation (often called “observational equivalence” in the literature).

Canonical map (selected terms)
------------------------------

| Literature term | LogOS wording (canonical) | LogOS identifier(s) | Default strength | “Textbook-strength” upgrade |
|---|---|---|---|---|
| preorder | preorder | `ConPreorder` (`LogOS/Minimal/Con.agda`) | preorder (no antisymmetry) | add `PartialOrder` when you want antisymmetry |
| poset | partial order | `PartialOrder` (`LogOS/Minimal/Con.agda`) | not assumed | supply antisymmetry explicitly |
| entailment | refinement / entailment | code refinement (`γ ⊢ δ`) / boundary refinement (`c ⊑ d`) | directed (irreversible) | equality-level only under antisymmetry/proof-irrelevance |
| (observational) equivalence | observational equality | `ObsEq…`, `≈∂`/`≈∂Cosp` (boundary), scheme `Sch.ObsEq` | satisfaction-induced relation | keep distinct from `≈` (mutual refinement) |
| homotopy / homotopical (HoTT) | “homotypical” (LogOS term) | H-tier truth `Sat_H (w , c)` + invariance `Inv_H` | world-indexed satisfaction + explicit invariance projector | HoTT axioms (univalence/HITs) are never assumed globally; any extensionality is explicit |
| adjunction | lax adjunction | `LaxAdjunction` (`LogOS/Minimal/Adjunction.agda`) | inequalities (lax unit/counit) | use `GaloisConnection` (↔-law) or add triangle laws as an explicit strengthening |
| Galois connection | Galois connection (tight form) | `GaloisConnection` (`LogOS/Minimal/Adjunction.agda`) | optional | requires monotonicity; still preorder-based |
| Beck–Chevalley | lax Beck–Chevalley | `LogOS/Theorems/CategoryTheory/BeckChevalley.agda` | commutes up to refinement | equality-level only under explicit extensionality assumptions |
| Frobenius reciprocity | lax Frobenius (inequality) | `AdjunctionMonads.Frobenius.*` (`LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda`) | one-way ≤ statement | equality-level only under explicit extensionality assumptions |
| quantale | unital finite-join quantale (quantale-like; not complete) | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | finite joins only | completeness is not assumed in the core |
| nucleus / local operator | closure operator / nucleus (preorder-level) | `ClosureOp` / `Flow` (guarded closure) | preorder-first | meet-preservation / other laws must be added explicitly when needed |
| ωCPO / dcpo | ωCPO structure | `OmegaCPO` + `FiniteFirst` (`LogOS/Minimal/Truth.agda`) | optional | provides Kleene μ and μ-induction principles |
| Kleene μ | Kleene μ = least pre-fixed point | `μ` (`LogOS/Minimal/Truth.agda`) | only under ωCPO hypotheses | “μ is fixed up to refinement” only after stating the unfold/continuity hypotheses |

μ / continuity (canonical phrasing)
-----------------------------------
In this repository, the unqualified phrase **“μ F”** always refers to the **Kleene** construction:

- `μ F` is the **least pre-fixed point** of `F` (i.e. least `x` such that `F x ⊑ x`) in the relevant preorder.
- Any statement of the form “μ is fixed up to refinement” is only made once the corresponding
  unfold/continuity hypotheses are stated (e.g. “unfold-right” / ω-continuity assumptions).

For stability objects in the kernel (e.g. `Th*` for `Flow`), the docs use:
- “distinguished lax fixed-point witness” by default, and
- “Kleene μ / least pre-fixed point” only under explicit ωCPO/continuity bundles
  (e.g. `LogOS/Theorems/Boundary/ContinuityCore.agda`, `LogOS/Theorems/Boundary/MuFusion.agda`).

H-tier indexing (canonical phrasing)
------------------------------------
When the docs say **H-tier truth**, they mean *world-indexed* satisfaction:
- `Sat_H (w , c)` where `w` is a world/context and `c` is a boundary constraint.

When the docs say **boundary-indexed H-tier truth**, they mean:
- `Sat_H_bnd (to∂ w , c)` and the coherence law `sat-coh`.

This distinction matters because `Sat_H` is easy to misread as already boundary-indexed.
