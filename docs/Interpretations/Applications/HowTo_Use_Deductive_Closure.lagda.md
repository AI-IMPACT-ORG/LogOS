<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% How-to: Use Deductive Closure (ZFC pack)

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Applications.HowTo_Use_Deductive_Closure where

open import LogOS.API.LT
open import LogOS.API.Reification using (quoteQP)
import LogOS.API.Theorems.Core as Theorems

open import LogOS.Apps.ZFC.Proof.Syntax
open import LogOS.Apps.ZFC.Proof.Axioms
import LogOS.Apps.ZFC.Proof.System as Proof

open Proof using
  ( Theory
  ; DerivesT; hypT
  ; theoryClosure
  ; ClosedTheory; closeTheory; theoryOf
  ; FlowTheory⊑closeTheory-eval
  )

-- Kernel-native base: keep this empty and put *all* assumptions in the ledger.
Base : Formula → Set
Base _ = ⊥

-- A ledger is a theory predicate.
LedgerZF : Theory
LedgerZF = TheoryAxiom

-- Close the ledger under modus ponens (a guarded closure transformer).
ClosedZF : ClosedTheory Base
ClosedZF = closeTheory Base LedgerZF

-- Membership in `theoryOf ClosedZF` is "provable from the ledger".
extensionality-in-Closed : theoryOf ClosedZF extensionalityF
extensionality-in-Closed =
  FlowTheory⊑closeTheory-eval Base LedgerZF extensionalityF
    (hypT (axZFCore axExtensionality))

-- The closure itself is a transformer; it induces canonical quotation.
qp = quoteQP (theoryClosure Base)

-- The closure fiber is contractible, so quotation witnesses no-fork up to observation.
module M = Theorems.ClosureKernelCentering (theoryClosure Base)

noFork-realisers : ∀ {R S : M.QC.QuoteWitness} → M.QC._≈R_ R S
noFork-realisers {R} {S} =
  Theorems.contractible⇒noSemanticFork M.fiber {x = R} {y = S}
```

Steps
-----

- Import the ZFC stack interface (`LogOS.Apps.ZFC.Stack`).
- Select a closure/flow doctrine for the boundary; the same object is also a
  `KZModality` and an `Effectivity` surface (`theoryKZ`, `theoryEffectivity`).
- Use `LogOS.Apps.ZFC.SetTheory.Definable` for Separation/Replacement.

Pointers
--------

- `LogOS/Apps/ZFC/Stack.agda`
- `LogOS/LT/Flow.agda`
- `LogOS/Apps/ZFC/SetTheory/Definable.agda`
