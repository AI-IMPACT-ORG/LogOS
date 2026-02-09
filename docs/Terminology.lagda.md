<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
- `docs/Applications/*` (packs).

The goal is not to impose one literature vocabulary, but to make the adapter
choices explicit and repeatable.

Interpretation (analogy): the tables below are a vocabulary crosswalk and
design discipline, not theorem statements; “literature ↔ LogOS” alignment is an
explicit interpretation boundary.

Quick conventions
-----------------
- **Judgmental equality** = Agda’s built-in conversion used by typechecking (not written as a symbol in the prose).
- **Propositional equality** = `_≡_` (proof-relevant).
- **Refinement** = preorder relation `_⊑_`.
- **Mutual refinement** = `≈` (two refinements).
- **Satisfaction equivalence** = `P ↔ Q` (paired implications).
- **Isomorphism** (in prose): reserve for explicit `≡`-level structure; otherwise say “adapter equivalence (`Adapter≈`)” or “quasi-inverse up to `↔`”.
- **`iff` / `\iff` in prose**: when used for satisfaction statements, read it as a `↔` (paired implications), not as a judgmental equality claim.
- **Observational equality** = a satisfaction-induced relation used as equality (often called “observational equivalence” in the literature).

Cross-discipline crosswalk (same artifact, different instincts)
--------------------------------------------------------------

| Concept | Logician instinct | Systems instinct | PL instinct | LogOS “anchor” |
|---|---|---|---|---|
| core interface | theory + semantics | API contract + trust boundary | language interface + semantics hooks | `KernelShape` / `Kernel` |
| entailment / refinement | `⊢` / consequence | monotone dependency / compatibility order | refinement / simulation preorder | `_⊑_` (and `Code≤` for code) |
| equivalence | `↔` / judgmental equality vs theorem | observational equality | contextual equivalence / observational equality | `↔`, `ObsEq…`, and `≈` (mutual refinement) |
| translation | interpretation / institution morphism | adapter boundary | compiler pass / IR translation | ports/interlingua + `SatMor` / `PresentationC` |
| modality / closure | `□`, `μ`, fixed points | stabilization / invariants / convergence | closure operator / least pre-fixed point (Kleene μ) semantics | `Box`, `Th*`, Kleene `μ` (under ωCPO assumptions) |
| controlled feedback / cybernetics | controlled feedback (“compute-then-stabilise”) | `FlowCode = Guard ∘ Body`, `decode-FlowCode`, step-grade `BoxAt step (Body _)` | kernel interface laws (commutation + closure at `sat`) | add `BudgetedTier` for grade monotonicity/composition; add ωCPO bundles when using Kleene `μ` |
| component / transducer | logic transformer (component view) | `docs/Views/ControlledFeedback.lagda.md` (`LogicTransformer`) | vocabulary/packaging only (no new axioms) | n/a (it is a documentation bundle) |
| assumptions | axioms and metatheorems | dependency/attack surface | semantic restrictions / meta assumptions | `LogOS.Theorems.Meta.ConditionalPacks` vs `...Assumptions.*` |

Canonical map (selected terms)
------------------------------

| Literature term | LogOS wording (canonical) | LogOS identifier(s) | Default strength | “Textbook-strength” upgrade |
|---|---|---|---|---|
| preorder | preorder | `ConPreorder` (`LogOS/Minimal/Con.agda`) | preorder (no antisymmetry) | add `PartialOrder` when you want antisymmetry |
| poset | partial order | `PartialOrder` (`LogOS/Minimal/Con.agda`) | not assumed | supply antisymmetry explicitly |
| system (open system) | open boundary system | `System` (`LogOS/System.agda`) | packages `BoundaryIO` + ambient signature/world/truth data | n/a (it is a packaging choice) |
| satisfaction system | satisfaction system (Ctx/Con/Sat triple) | `SatSystem` + `satSystem` (`LogOS/Ports/Semantic/PresentationCore.agda`) | explicit; kernel-independent | n/a (it is a packaging choice) |
| entailment | refinement / entailment | code refinement (`γ ⊢ δ`) / boundary refinement (`c ⊑ d`) | directed (irreversible) | equality-level only under antisymmetry/proof-irrelevance |
| (observational) equivalence | observational equality | `ObsEq…` (presentation, `↔`) and `≈`/`Obs≈…` (two-way refinement in an observational preorder) | satisfaction-induced relation | keep distinct from `≡` (strict); reserve `↔` for propositions |
| mechanisable (effective) | mechanisable (relative to a chosen universal stepper/observation) | `ObsKit` (`LogOS/UniversalIR/ObservedKernel.agda`) | interface-level assumption | supply an explicit physics/realizability model that produces an `ObsKit` |
| homotopy / homotopical (HoTT) | “homotypical” (LogOS term) | H-tier truth `Sat_H w c` + invariance `Inv_H` | world-indexed satisfaction + explicit invariance projector | HoTT axioms (univalence/HITs) are never assumed globally; any extensionality is explicit |
| adjunction | lax adjunction | `LaxAdjunction` (`LogOS/Minimal/Adjunction.agda`) | inequalities (lax unit/counit) | use `GaloisConnection` (↔-law) or add triangle laws as an explicit strengthening |
| Galois connection | Galois connection (tight form) | `GaloisConnection` (`LogOS/Minimal/Adjunction.agda`) | optional | requires monotonicity; still preorder-based |
| Beck–Chevalley | lax Beck–Chevalley | `LogOS/Theorems/CategoryTheory/BeckChevalley.agda` | commutes up to refinement | equality-level only under explicit extensionality assumptions |
| Frobenius reciprocity | lax Frobenius (inequality) | `AdjunctionMonads.Frobenius.*` (`LogOS/Theorems/CategoryTheory/AdjunctionMonads.agda`) | one-way ≤ statement | equality-level only under explicit extensionality assumptions |
| prequantale | unital finite-join prequantale (not complete) | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | finite joins only | completeness is not assumed in the core |
| nucleus / local operator | closure operator / nucleus (preorder-level) | `ClosureOp` / `Flow` (guarded closure) | preorder-first | meet-preservation / other laws must be added explicitly when needed |
| ωCPO / dcpo | ωCPO structure | `OmegaCPO` + `FiniteFirst` (`LogOS/Minimal/Truth.agda`) | optional | provides Kleene μ and μ-induction principles |
| Kleene μ | Kleene μ = least pre-fixed point | `μ` (`LogOS/Minimal/Truth.agda`) | only under ωCPO hypotheses | “μ is fixed up to refinement” only after stating the unfold/continuity hypotheses |
| locally preordered 2-category | thin 2-category | `RelThin2Cat` (`LogOS/Minimal/RelThin2Cat.agda`) (and the same-universe specialization `Thin2Cat`) | ops-first; laws are ≈-level | equality-level laws only under antisymmetry/proof-irrelevance |
| refinement 2-category (wrapper) | refinement 2-category core | `Ref2CatCore` + (`Thin2Cat→Ref2CatCore` / `RelThin2Cat→Ref2CatCore`) (`LogOS/Theorems/CategoryTheory/WrapperCore.agda`) | packaging only | n/a (it is a wrapper) |

Transformer (GenAI) (terminology)
---------------------------------
In the Agents experimental pack, “transformer” refers to the standard neural
attention architecture, formalized as an explicit interface:

- `LogOS/Packs/Agents/Experimental/Arguments/TransformerFormalization.agda`
  (`TransformerCore`: tokens/parameters/forward + kernel-native encoding).
- `LogOS/Packs/Agents/Experimental/Arguments/TransformerBridge.agda`
  (multi-head attention skeleton + bridge to kernel policies/codes).
- Narrative entrypoint: `docs/Applications/Agents_Experimental.lagda.md`.

Do not confuse this with the **logic transformer** label used in
`docs/Views/ControlledFeedback.lagda.md`, which is a kernel-side controlled-feedback
interface vocabulary bundle.

Interpretation (analogy):
both stories reuse “stability under an explicit step” as a design pattern, but
they live at different layers (kernel interface vs ML architecture/training).

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
- `Sat_H w c` where `w` is a world/context and `c` is a boundary constraint.

When the docs say **boundary-indexed H-tier truth**, they mean:
- `Sat_H_bnd (to∂ w) c` and the coherence law `sat-coh`.

In prose, we may write $Sat_H(w,c)$ / $Sat_H_bnd(to∂ w,c)$ to emphasize the two arguments; the Agda interface is curried.

This distinction matters because `Sat_H` is easy to misread as already boundary-indexed.
