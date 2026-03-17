<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# View family: Logic, Programming, and Type Theory

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Views.Logic_Programming_And_Type_Theory where

import LogOS.API.LT
```

This umbrella view collapses the earlier Curry-Howard-Lambek, derivability,
programming-theory, proof-theory, institution-fragment, and type-theory notes
into one reader-facing surface.

What is actually defined
------------------------

- **Type-theoretic spine**: a refinement-first tower from `ConPreorder` up to
  kernels, morphisms, and ports, encoded inside Agda.
- **Programming-theory reading**: kernels as implementations paired with
  observable semantics, and kernel morphisms as certified translations.
- **Derivability / proof theory**: optional presentation layers, rule-generated
  closures, suite-indexed proof systems, presentation independence, and
  explicit quotation/reification capabilities.
- **Curry-Howard-Lambek bridge**: a boundary-first semantics of
  types/propositions/programs, without identifying those levels by fiat.
- **Institution fragment**: optional packaging of signatures, sentences, and
  models over the refinement-first kernel interface.

Literature reading
------------------

- boundaries play the role of observed judgements/propositions/interfaces;
- code is the internal realiser/program layer and `KernelHom` is
  semantics-aware translation;
- derivability and proof systems are explicit overlays that must justify
  themselves against observation;
- proof systems and presentation layers can be transported along
  meaning-preserving translations instead of being fixed ambiently;
- deductive closure now reuses the same closure/KZ/effectivity vocabulary as
  the rest of the LT core (`theoryClosure`, `theoryKZ`, `theoryEffectivity`,
  and the Metamath-facing `mmEffectivity` are different interfaces to the same
  guarded-closure spine);
- institution-style satisfaction is available as a fragmentary, forward
  transport discipline over the same base.

Where LogOS is weaker or more general
-------------------------------------

- there is no standalone object language, parser, or judgemental equality in
  the spine;
- refinement `⊑` and mutual refinement `≈` are primary, with strict equality
  only as an explicit late check;
- quotation, reification, and completeness are opt-in structure, not ambient
  meta-theory;
- institution-style transport is forward and refinement-first rather than a
  textbook contravariant reduct story.

What is not claimed
-------------------

- no global Curry-Howard-Lambek equivalence theorem for the repository;
- no built-in lambda calculus, CCC structure, sequent calculus, cut
  elimination, or normalisation theorem;
- no complete directed type theory calculus as a separate object language;
- no full institution with textbook satisfaction condition as primitive
  structure.

Code anchors
------------

- `LogOS/LT/ConPreorder.agda`
- `LogOS/LT/View.agda`
- `LogOS/LT/Kernel.agda`
- `LogOS/LT/Hom.agda`
- `LogOS/LT/Derivability.agda`
- `LogOS/LT/Presentation.agda`
- `LogOS/LT/Presentation/ObservationInitiality.agda`
- `LogOS/LT/Presentation/Interlingua.agda`
- `LogOS/LT/Presentation/Independence.agda`
- `LogOS/LT/InstitutionFragment.agda`
- `LogOS/LT/Theory/Rules.agda`
- `LogOS/LT/Theory/HilbertMP.agda`
- `LogOS/Ports/Reification/GuardedLawvere.agda`
- `docs/Patterns/Clarifications/Directed_Type_Theory.lagda.md`
