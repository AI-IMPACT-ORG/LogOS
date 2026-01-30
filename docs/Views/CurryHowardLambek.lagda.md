<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Curry–Howard–Lambek (CHL Capstone)

```agda
{-# OPTIONS --safe #-}
module docs.Views.CurryHowardLambek where

-- Typechecked “view surface” for the Curry–Howard–Lambek presentation.
--
-- Keep this module lightweight to avoid name clashes when imported alongside
-- other views/tests.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheorems

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = ViewTheorems.For K
  open V.CHL public

  private
    capstone-exists : _
    capstone-exists = capstone

    capstone-complete-exists : _
    capstone-complete-exists = capstone-complete

    capstone-complete-budget-exists : _
    capstone-complete-budget-exists = capstone-complete-budget

    completeF-exists : _
    completeF-exists = completeF

    completeF-budget-exists : _
    completeF-budget-exists = completeF-budget

    formula-program-exists : _
    formula-program-exists = formula-program

    formula-sat-boundary-exists : _
    formula-sat-boundary-exists = V.Commuting.formula-sat-boundary

    projection-exists : _
    projection-exists = V.Projections.projection
```

Purpose
-------
This view presents the LogOS kernel as a Curry–Howard–Lambek-style “single
system”: propositions/types, proofs/programs, and entailment/computation are
all read off one interface. The presentation is deliberately preorder-safe:
the native notion of consequence is refinement (`⊑`) and mutual refinement
(`≈`), not equality of proofs/terms.

See also: `docs/Views/MeredithSentences.lagda.md` (ultra-compact “axiom poem”
presentation of the CHL-facing `LogicKernel`, derived from any `Kernel` via
`LogOS/Kernel/LogicKernel/FromKernel.agda`).

Interpretation (analogy):
this document is a derived presentation (“view”) over the same kernel interfaces;
it does not add logical power.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Notation (local)
----------------
- `c ⊑ d`: refinement/entailment in a preorder.
- `c ≈ d`: mutual refinement (two refinements).
- `P ↔ Q`: satisfaction equivalence (paired implications).
- `x ≡ y`: propositional equality (`_≡_`), not judgmental equality.

Scope (formal)
--------------
- Parameter: `Kernel Sig Q`.
- Surface: `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CHL`).

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| Propositions / types | boundary constraints `Con_bnd`, strict formulas `Fml` | LogOS keeps S (strict) and H/∂ (boundary) layers explicit. |
| Proofs / programs | `Code` (kernel code) | “Programs as proofs” is internalised as code + refinement. |
| Entailment / derivability | code refinement `γ ⊢ δ`, boundary entailment (`Entails∂`) | Primary notion is directed refinement, not equality. |
| Modality □ / closure | `Box` (ungraded), `BoxAt` (graded/LogicKernel) | `Box γ = encode (Flow (decode γ))` (`LogOS/Kernel.agda`). In the CHL-facing `LogicKernel`/graded setting: `BoxAt g γ = encode (Flow g (decode γ))` (`LogOS/Kernel/LogicKernel.agda`). |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital quantale in the finite-join sense (not complete); used by graded/budgeted variants. |
| Soundness / completeness | `capstone`, `completeF`, budgeted variants | Completeness requires explicit (budgeted) adequacy assumptions. |
| Presentation-independence | ports/adapters + interlingua | Boundary truth (`Sat_H w c` and boundary-indexed `Sat_H_bnd (to∂ w) c`) is transported across ports via satisfaction equivalence (↔). |

Core definitions (literature style)
-----------------------------------

**Definition (Refinement entailment).** The CHL-facing consequence relation is
refinement on code:
\[
  \gamma \vdash \delta \;:=\; \gamma \;\;⊑\;\; \delta
\]
in the code preorder. This is definable because `Code` comes with a refinement
relation and its laws (identity/cut) in the CHL surface (`LogOS/Theorems/Meta/CHL/Definition.agda`).

**Definition (Closure/modality).** The “□” operator is the kernel’s closure on
code:
\[
  \Box(\gamma) := \mathrm{encode}(\mathrm{Flow}(\mathrm{decode}(\gamma))).
\]
Graded/budgeted variants use `BoxAt g`.

**Definition (Adequacy/completeness scope).** Any completeness statement in
this view is explicitly *relative* to an adequacy assumption (plain or budgeted)
on the chosen boundary observation regime; it is never a global kernel axiom.

Assumptions (explicit)
----------------------
- No proof-irrelevance or antisymmetry is assumed; refinement is directed and proof-relevant.
- Completeness is conditional: it requires explicit adequacy hypotheses (plain or budgeted).
- Whenever this note says “complete”, read it as “complete relative to the stated adequacy hypothesis”.
- No surjectivity is assumed for translations like `TransH` or `to∂`.

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: the CHL triangle (propositions/types, proofs/programs, entailment) as an internal kernel view.
- Weaker/lax by default: all statements are up to refinement/mutual refinement (`≈`), not judgmental equality; closure is a preorder-level modality.
- Added by ports/adapters: “compute-then-stabilise” is explicit (`Step = Box ∘ Body`, equal after decoding (≡) to `FlowCode`), and translations between presentations are forced/unique up to satisfaction equivalence (↔).
- Assumption-scoped: completeness is conditional (plain or budgeted adequacy), never a global kernel axiom.

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CHL`):
  `capstone`, `capstone-complete`, `capstone-complete-budget`,
  `completeF`, `completeF-budget`, `formula-program`.
- Commuting square with the institution view:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Commuting`),
  `formula-sat-boundary`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- The prose below is explanatory; the statements above are the authoritative claims.

Micro-example (a commuting “step” square)
-----------------------------------------
This view uses two equally LogOS-native “one-step” operators on code:

- `RawStep = FlowCode` (operational step: `Guard ∘ Body`), and
- `Step = Box (Body _)` (“compute then stabilise” at the step grade).

The CHL surface proves they coincide after decoding (so they induce the same
decoded behaviour), and then packages observer predicates so they depend only on
the decoded step up to mutual refinement; see `LogOS/Theorems/Meta/CHL/Core.agda`
(`decode-RawStep≡decode-Step`) and `docs/Views/ObserverSemantics.lagda.md`.

Pointers (no repetition)
------------------------
- Kernel/tier bookkeeping: `docs/LogOS_Core_Spec.lagda.md`.
- μ/limit facts and hypotheses: `docs/Terminology.lagda.md` and `docs/Kernel/ClaimRegister.lagda.md`.
- Completeness surfaces (assumption-scoped): `LogOS/Theorems/Meta/CHL/Completeness.agda`, `LogOS/Theorems/Meta/CHL/SyntaxCompleteness.agda`.
- Bootstrapping/interoperability: `LogOS/Theorems/Meta/CHL/Interoperability.agda`, `LogOS/Theorems/Meta/Bootstrapping.agda`.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
  - Meredith sentences: `docs/Views/MeredithSentences.lagda.md`
  - Multi-institution: `docs/Views/MultiInstitution.lagda.md`
  - Categorical logic: `docs/Views/CategoricalLogic.lagda.md`
  - Observer semantics: `docs/Views/ObserverSemantics.lagda.md`

Legacy notes (kept short)
-------------------------
The longer “concept flow” narrative for budgeted adequacy is unchanged in the
code; this view now treats it as a pointer rather than duplicating it. If you
want the single packaged theorem, see `LogOS/Theorems/Meta/CHL/Capstone.agda`.
