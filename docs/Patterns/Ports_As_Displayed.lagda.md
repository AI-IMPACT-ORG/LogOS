<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: Ports as displayed structures

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Ports_As_Displayed where

import LogOS.API.LT
```

Decision
--------

- Implement ports/adapters as **displayed thin 2-categories over a chosen base thin 2-category**.
- Treat ports as optional, composable structure that must not change refinement.

Mechanics
---------

- Base graph: a chosen thin 2-category (`LOG`, `LOGᴳʳ`, or another explicit base).
- Port = displayed structure over that base (displayed objects + displayed morphisms).
- Totalisation = decorated component graph; refinement inherited from base.

In public-facing examples, many ports are still first authored on `LOG` and
then reindexed to `LOGᴳʳ` via `LogOS/LT/LOG/PortReindexing/Strictification.agda`. That is a
basis choice, not the primitive definition of “displayed port”.

Canonical constructors (normal form)
------------------------------------

- `DisplayedThin2Cat` — displayed structure over a base.
- `ProductDisplayed` — product of displayed structures (stacking ports).
- `DecoratedThin2Cat` — totalised displayed thin 2-category.
- `SuccessorStage` — name the one-step “displayed layer + Σ-totalisation” move when it should be reused as a stage constructor.
- `forgetDecorated` — projection back to base.

Packaging: tagged ports and capability-first stacks
---------------------------------------------------

For a uniform, capability-first surface over these primitives, LogOS uses:

- `PortSig` (`LogOS/LT/Ports/PortSig.agda`): a displayed layer tagged by a type-level label.
- `PortStack` (`LogOS/LT/Ports/PortStack.agda`): a non-empty, right-associated stack of `PortSig` entries.

Naming discipline:
when a stack needs raw lookup, leftmost shadowing, or no-dup, LogOS uses a
small first-order name for that bookkeeping and packages the richer dependent
semantics in the full entry. In the current port stack this means:

- `PortLabel` carries raw identity,
- `PortEntry` carries the full dependent semantics,
- `Member` is label-based raw lookup,
- `EntryMember` is exact typed membership.

This is now a deliberate LT pattern rather than an accidental implementation
detail; see `docs/Patterns/First_Order_Names_And_Dependent_Payloads.lagda.md`.

Universe note:
`PortSig` is universe-polymorphic in its tag (`Tag : Set ℓTag`) and stores the displayed object/hom
levels as part of its data; the port infrastructure therefore lives in `Setω`.

`PortStack` folds definitionally to a right-associated `ProductDisplayed`, but additionally provides:

- a stable projection vocabulary (`HasPort`, `getObj`, `getHom`, `forgetPort`, `forgetSubstack`),
- a standard “subtyping by forgetting” discipline (forgetful functors are structural projections),
- guardrails: future refactors can keep definitional equalities stable (see discipline gates).

Design rule (capabilities-first):
downstream ports/apps should not pattern-match on nested Σ-shapes (`fst`/`snd`) of stacked objects/morphisms.
Use `HasPort` + `getObj/getHom` instead.

Authoring templates
-------------------

To keep `*2Cat` port modules uniform (and to make “discipline gates” stable), LogOS provides
small record templates:

Ordinary ports are the **static special case** of successor-stage totalisation: the displayed layer is
chosen once, totalised once, and exported through the templates below. Generated hierarchies reuse the
same one-step construction repeatedly via `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`.

- `LogOS/LT/Ports/Template/Singleton2Cat.agda` — package a singleton displayed layer as a port stack.
- `LogOS/LT/Ports/Template/Stack2Cat.agda` — package a composite `PortStack` as a port stack.
- `LogOS/LT/Ports/Template/LawSingleton2Cat.agda` — singleton “law ports” where the displayed hom payload is a law `Law f`.

Successor stages and cumulative hierarchies
-------------------------------------------

When a downstream theory wants a **next stage** generated from admissible
structure on a current stage, reuse the same LT move that already packages
ordinary ports:

- choose a displayed layer over the current stage,
- totalise it once,
- inherit refinement from the base,
- and only add closure/fixed-point machinery when that extra doctrine is
  really needed.

This keeps the codebase self-similar: ordinary ports are the **static special
case** of successor-stage totalisation, while generated hierarchies reuse the
same move intentionally as a ladder.

Relevant constructors and downstream examples:

- `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`
- `LogOS/LT/Presentation/GeneratedSubobject/Core.agda`
- `LogOS/LT/Presentation/GeneratedImage.agda`
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/Hierarchy.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda`

If a theory needs actual generated closure/effectivity doctrine, add it
*after* the stage step:

- `LogOS/LT/Sup/AbstractGeneratedClosure.agda`
- `LogOS/LT/Effectivity.agda`
- `LogOS/LT/Theorems/StableCompletion.agda`

Product ports vs law ports
--------------------------

There are two different composition patterns, and conflating them is a common
source of accidental coupling and awkward forgetful maps.

**Product ports** are for strictly independent layers:

- there is no coupling law that mentions both layers at once;
- forgetting either layer should be canonical and structure-free.

Normal form:

- define a `PortStack` of tagged ports,
- build the displayed product via `PortStack.StackDisplayed`
  (definitionally a right-associated `ProductDisplayed`),
- totalise once,
- project via `PortStack.forgetPort`.

**Law ports** are for “existing layer(s) + an additional linking law”:

- the displayed objects/morphisms are not a plain product of independent
  structure;
- the new layer ties previously independent components together.

Normal form:

- define the law port via `LawDisplayed` or `LawDisplayedOn`,
- totalise once,
- provide explicit forgetful 2-functors back to each independent component.

Canonical examples:

- Quote port (flow + encode + linking law): `LogOS/LT/LOG/QuotePort2Cat.agda`
- Landauer layer as a law-port: `LogOS/Ports/AbstractLandauer2Cat.agda`
- Purification witnesses as a law-port with explicit witness calculus:
  `LogOS/Ports/PreQuantum/Purification2Cat.agda`

Decision rule (copy-paste criterion)
------------------------------------

- If you want “concern A and concern B, independently”: use `PortStack`
  (definitionally `ProductDisplayed`).
- If you want “concern A and concern B, plus a statement relating them”: use
  `LawDisplayed`/`LawDisplayedOn` and export explicit forgetfuls.

Guardrail: refinement must stay weak
------------------------------------

- `⊑` is primitive; `≈` is mutual refinement; `≡` is S-tier only.
- Displayed evidence does **not** participate in `_⊑_` on total morphisms.

Pointers
--------

- `LogOS/LT/DisplayedThin2Cat.agda`
- `LogOS/LT/DisplayedThin2Cat/Totalisation.agda`
- `LogOS/LT/LOG/PortReindexing/Strictification.agda` (strict pullback along `toLOG` to obtain LOGᴳʳ-based ports)
- `LogOS/LT/Ports/PortSig.agda`
- `LogOS/LT/Ports/PortStack.agda`
- `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`
- `LogOS/LT/Presentation/GeneratedSubobject/Core.agda`
- `LogOS/LT/Presentation/GeneratedImage.agda`
- `LogOS/LT/LOG/QuotePort2Cat.agda`
- `LogOS/Ports/AbstractLandauer2Cat.agda`
- `LogOS/LT/Discipline/PortStackFolding.agda` (discipline gate; typecheck-only)
- `LogOS/LT/Discipline/SuccessorStageFolding.agda` (discipline gate; typecheck-only)
- `LogOS/LT/Discipline/HomDefaults.agda` (discipline gate; typecheck-only)
