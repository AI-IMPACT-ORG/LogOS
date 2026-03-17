<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# How to Add a Port

Use this checklist when introducing a new port in `LogOS/Ports/**` or a displayed port over an explicit thin 2-category basis.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.HowTo.HowTo_Add_Port where

import LogOS.API.LT
```

## 1) Choose the port shape

- Plain view port: use when the port is only an observation boundary.
- Displayed port: use when objects and morphisms both need extra structure/coherence over a chosen base (`LOG`, `LOGᴳʳ`, or another explicit thin 2-category).
- Generated stage: use `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda` when the same displayed-totalisation step should be reused as a hierarchy constructor rather than exported as one static port.
- Choose the **basis** explicitly (LOG vs LOGᴳ) and justify it.
  Internal ports should default to LOGᴳ; applications/physics may opt for LOG.

## 2) Plain view port checklist

- Define a record in `LogOS/Ports/*.agda` whose primary field is a `View`.
- Provide induced relations (`_⊑..._`, `_≈..._`, `_≃..._`) as pullbacks.
- Provide `PullbackPreorder`-based preorder packaging when useful.
- If this port corresponds to theorem-level probe suites, expose a bridge lemma.

## 3) Displayed port checklist

- Define displayed objects and displayed morphisms in a `LOG*` module under `LogOS/LT/**`.
- Use the canonical packaging:
  - define a tag type `…Tag` (1-constructor datatype),
  - define `…Sig : PortSig (LOG …) …Tag`,
  - for singleton ports, **prefer the templates**:
    - define `port2Cat : Template.Singleton2Cat (LOG …) …Tag`,
    - define `port2Cat = Template.mkSingleton2Cat …Sig`,
    - expose the record fields by opening it:
      - if `port2Cat` is polymorphic in levels, use a named wrapper module:
        - `module Port {…} where open Template.Singleton2Cat (port2Cat {…}) public`
        - `open Port public using (singleton; stack; port; Displayed; WithPort; forget)`
      - otherwise, just:
        - `open Template.Singleton2Cat port2Cat public using (singleton; stack; port; Displayed; WithPort; forget)`
  `LogOS/LT/Ports/Template/Singleton2Cat.agda` provides a mechanically correct packaging helper
  for the default refinement-facing surface. Keep `displayed≡`-style bookkeeping
  witnesses in an explicit `Definitional` sibling rather than on the default public lane.
  For law ports (where the displayed hom payload is a proof `Law f`), prefer
  `LogOS/LT/Ports/Template/LawSingleton2Cat.agda` (based on `LawDisplayedOn` with an explicit unit type,
  to avoid `⊤`/`tt` footguns in composed stacks).
  For composite ports (stacked ports), prefer `LogOS/LT/Ports/Template/Stack2Cat.agda`.
  These templates are the static special case of `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`: if you
  are not exporting a fixed port but a reusable “next stage” constructor, use `SuccessorStage` directly.
  This makes all `*2Cat` ports uniform and keeps projections capability-first.
- Keep 2-cells inherited from the chosen base unless stronger coupling is intended.
  For LOG-basis ports this is boundary-driven `_⇒∂_`; implementation-first `_⇒_` is the equivalent derived view.
- If you need a LOG-basis port on the internal `LOGᴳʳ` basis, add an architecture-first wrapper module by strict pullback along
  `toLOG : LOGᴳʳ → LOG` using `LogOS/LT/LOG/PortReindexing/Strictification.agda`:
  - use `reindexDisplayedStrictF (toLOGStrict …)` to reindex a raw displayed layer (or `pullbackPortSigAlongToLOG` /
    `pullbackPortEntryAlongToLOG` / `pullbackPortStackAlongToLOG` for packaged ports), and
  - obtain the weakening functor back to the LOG-basis via `weakenDecoratedAlongToLOG`.
  Use the canonical architecture-first module name directly.
  Avoid writing bespoke `mapObj′/mapHom′` weakening functors in port modules.
  If a functor law proof reduces to “these have the same `baseHom`”, use
  `DisplayedThin2Cat.baseHom≡→total≈` rather than a local lemma.

## 4) Composition checklist

- If composing with existing ports, use `PortStack` (`LogOS/LT/Ports/PortSig.agda`, `LogOS/LT/Ports/PortStack.agda`).
  (`ProductDisplayed` is the underlying primitive; prefer `PortStack` for typed capabilities + forgetting.)
- For a composite port module that packages a `PortStack` as a thin 2-category, prefer
  `LogOS/LT/Ports/Template/Stack2Cat.agda` instead of bespoke `LOG…`/`forget…` aliases.
- Add only the combined object/morphism projections needed by downstream apps.
- Avoid introducing bespoke refinement relations when pullback/inherited relations suffice.

## 5) Docs and API checklist

- Add/update one note in `docs/Patterns/Ports_As_Displayed.lagda.md` if the design is new.
- If the new port is really a reusable stage constructor or a law-port pattern, document that in `docs/Patterns/Ports_As_Displayed.lagda.md` as well.
- Re-export the new port from `LogOS/API/Ports.agda`.
- Ensure `docs/Core/Spec/LogicalTransformers.lagda.md` imports any new `LogOS/LT/**` module.
