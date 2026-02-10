<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Kernel Claim Register (Literal vs Stabilised vs Representational vs Analogy)

```agda
{-# OPTIONS --safe #-}
module docs.Kernel.ClaimRegister where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.World as Worlds
import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)

open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.PresentationCore using (satSystem)

open import LogOS.Kernel using (Kernel; Box; Th*)

import LogOS.Boundary.KernelVacuityGuards as KVac
import LogOS.Ports.Semantic.VacuityGuards as PVac
import LogOS.QAdapters.Guards as QVac

import LogOS.Ports.Semantic.Interoperability as Interoperability
import LogOS.Theorems.Boundary.Stabilisation as Stabilisation

import LogOS.Minimal.Thin2Cat as Thin2Cat
import LogOS.Minimal.RelThin2Cat as RelThin2Cat
import LogOS.Theorems.CategoryTheory.WrapperCore as WrapperCore
import LogOS.Ports.Semantic.Presentation2Cat as Presentation2Cat
import LogOS.Computation.Process2Cat as Process2Cat
import LogOS.Theorems.Boundary.OmegaCPOMap2Cat as OmegaCPOMap2Cat
import LogOS.API.Bridges as Bridges

private
  thin2cat-comp-mono-exists : _
  thin2cat-comp-mono-exists = Thin2Cat.comp-mono

  relthin2cat-comp-mono-exists : _
  relthin2cat-comp-mono-exists = RelThin2Cat.comp-mono

  thin2cat→ref2catcore-exists : _
  thin2cat→ref2catcore-exists = WrapperCore.Thin2Cat→Ref2CatCore

  relthin2cat→ref2catcore-exists : _
  relthin2cat→ref2catcore-exists = WrapperCore.RelThin2Cat→Ref2CatCore

  presentationThin2Cat-exists : _
  presentationThin2Cat-exists = Presentation2Cat.For.PresentationThin2Cat

  presentationRelThin2Cat-exists : _
  presentationRelThin2Cat-exists = Presentation2Cat.For.PresentationRelThin2Cat

  processThin2Cat-exists : _
  processThin2Cat-exists = Process2Cat.For.ProcessThin2Cat

  processRelThin2Cat-exists : _
  processRelThin2Cat-exists = Process2Cat.For.ProcessRelThin2Cat

  omegaCPOThin2Cat-exists : _
  omegaCPOThin2Cat-exists = OmegaCPOMap2Cat.For.OmegaCPOThin2Cat

  omegaCPORelThin2Cat-exists : _
  omegaCPORelThin2Cat-exists = OmegaCPOMap2Cat.For.OmegaCPORelThin2Cat

  run∞-exists : _
  run∞-exists = Bridges.Limit.Process.For.run∞

  run∞-map≤-exists : _
  run∞-map≤-exists = Bridges.Limit.Process.TransportLax.run∞-map≤

  preserves-run∞-exists : _
  preserves-run∞-exists = Bridges.Limit.Sub2Cat.For.preserves-run∞

module _ {ℓ₁ ℓ₂ : Level} (CP₁ : ConPreorder ℓ₁) (CP₂ : ConPreorder ℓ₂) where
  module MF = Stabilisation.MuFusion.For CP₁ CP₂
  μ-fusion≤-exists : _
  μ-fusion≤-exists = MF.μ-fusion≤
  preserves-Th*-from-Flow-exists : _
  preserves-Th*-from-Flow-exists = MF.preserves-Th*-from-Flow
  Th*TransportAssumptions-exists : _
  Th*TransportAssumptions-exists = MF.Th*TransportAssumptions
  preserves-Th*-from-Flowᵃ-exists : _
  preserves-Th*-from-Flowᵃ-exists = MF.preserves-Th*-from-Flowᵃ

module _
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {Ctx₁ : Set ℓCtx₁}
  (CP₁ : ConPreorder ℓCon₁)
  {Sat₁ : Ctx₁ → ConPreorder.Con CP₁ → Set ℓSat₁}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {Ctx₂ : Set ℓCtx₂}
  (CP₂ : ConPreorder ℓCon₂)
  {Sat₂ : Ctx₂ → ConPreorder.Con CP₂ → Set ℓSat₂}
  (m  : SatMor
          (satSystem Ctx₁ (ConPreorder.Con CP₁) Sat₁)
          (satSystem Ctx₂ (ConPreorder.Con CP₂) Sat₂))
  (P₁ : PresentationC {ℓForm = ℓForm₁}
          (satSystem Ctx₁ (ConPreorder.Con CP₁) Sat₁))
  (P₂ : PresentationC {ℓForm = ℓForm₂}
          (satSystem Ctx₂ (ConPreorder.Con CP₂) Sat₂))
  where
  module Limit = Interoperability.Limit CP₁ CP₂ m P₁ P₂
  translate-μ≤-exists : _
  translate-μ≤-exists = Limit.translate-μ≤
  translate-μ≤↑-exists : _
  translate-μ≤↑-exists = Limit.translate-μ≤↑

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where
  box-exists : _
  box-exists = Box K
  th*-exists : _
  th*-exists = Th* (Kernel.G K)

  kernelVacuityGuards-exists : _
  kernelVacuityGuards-exists = KVac.KernelVacuityGuards K

module _
  {ℓ : Level} {ℓForm : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  where
  portVacuityGuards-exists : _
  portVacuityGuards-exists = PVac.PortVacuityGuards B P

module _ {ℓ : Level} {Q : QAdapter ℓ} where
  qAdapterVacuityGuards-exists : _
  qAdapterVacuityGuards-exists = QVac.QAdapterVacuityGuards Q
```

Reading discipline (guardrail)
------------------------------
This repository distinguishes four kinds of statements:

- **Literal (checked):** a definition/lemma typechecked by Agda.
- **Stabilised truth (closure):** a closure/fixed-point style statement (e.g. `Th*`, `Box`, Kleene `μ Flow`).
  By default, these are only *lax* fixed points (two inequalities), unless extra domain structure is assumed.
- **Representational truth (presentation):** a statement transported through ports/adapters (satisfaction equivalences (↔)),
  not judgmental equality of syntax/terms.
- **Analogy / interpretation:** explanatory metaphors; they never add logical power.

Notation (used throughout the docs): `≡` is propositional equality, `c ⊑ d` is (directed) refinement in a preorder,
`c ≈ d` is mutual refinement (two inequalities), and `P ↔ Q` is a satisfaction equivalence (paired implications).

Claim stamp sidecar format (CNL-lite):
<!-- CLAIM-STAMP: LITERAL | anchor=path#symbol -->
<!-- CLAIM-STAMP: STABILISED | anchor=path#symbol -->
<!-- CLAIM-STAMP: REPRESENTATIONAL | anchor=path#symbol -->
<!-- CLAIM-STAMP: ANALOGY | anchor=path#symbol -->
These sidecar comments are optional for prose in general, but required in the highest-risk public claims.
They are machine-checked by `make claim-stamp-check`.

Relation/equality governance (views + pullbacks): `docs/Kernel/RelationDiscipline.lagda.md`.
Canonical view registry (what relations are induced by what maps): `docs/Kernel/ViewRegistry.lagda.md`.
Canonical bridge registry (tier/repr/flow/limit vocabulary): `docs/Kernel/BridgeConcepts.lagda.md`.

This page is a compact “claim register”: it points to the **exact code surfaces**
that define what each phrase means.

## Kernel objects (literal)

- **Kernel shape:** `LogOS/Kernel/Shape.agda` (`KernelShape`).
  This is the “shared” interface: S/H truth, boundary constraints, and reflective code (`encode`/`decode`).
- **Kernel:** `LogOS/Kernel.agda` (`Kernel`).
  This repackages a kernel shape together with a parameterised guarded tier (`GTier`) so the same interface covers
  ungraded and graded kernels uniformly.

## Stabilised truth (closure; lax by default)

- **Operational code step:** `LogOS/Kernel/Shape.agda` (`FlowCode`) and `LogOS/Kernel.agda` (`FlowCode`).
  This is the one-step update on code (`Guard ∘ Body`).
- **Closure modality:** `LogOS/Kernel.agda` (`BoxAt`, `Box`).
  These are *code-level* modalities defined by `encode ∘ Flow ∘ decode`.
- **Distinguished “stable truth”:** `LogOS/Kernel.agda` (`GTier.Th*` / `Th*`).
  By default this is only a *lax fixed point* (`Th* ⊑ Flow sat Th*` and `Flow sat Th* ⊑ Th*`), not a least pre-fixed point.

If you want leastness/μ-induction strength (and to relate `Th*` to Kleene `μ`), the explicit domain-theoretic assumptions live in:

- `LogOS/Minimal/Truth.agda` (`OmegaCPO`, `FiniteFirst`, Kleene `μ`).
- `LogOS/Theorems/Boundary/ContinuityCore.agda` (connects `Th*` with Kleene `μ` under `FiniteFirst`/`OmegaCPO`).
- `LogOS/Theorems/Boundary/MuFusion.agda` (transport `μ` and derived `Th*` preservation under ω-continuous maps).

One key “assumption-complete” transport theorem is:

- **Derived stability transport (`Th*`):** `LogOS/Theorems/Boundary/MuFusion.agda` (`preserves-Th*-from-Flow`).
  This is a preorder-level statement (`⊑`), not an equality, and it is only available under explicit hypotheses:
  - `ω₁ : OmegaCPO CP₁`, `ω₂ : OmegaCPO CP₂` (ω-chain sups + bottom),
  - `M : OmegaCPOMap ω₁ ω₂ map` (monotone map + strict bottom + ω-continuity for sups),
  - `FF₁ : FiniteFirst CP₁ G₁ ω₁`, `FF₂ : FiniteFirst CP₂ G₂ ω₂` (connect `Th*` to Kleene `μ Flow`),
  - `comm : ∀ c → map (Flow₁ c) ⊑ Flow₂ (map c)` (lax step commutation).
  Under these assumptions it derives `map Th*₁ ⊑ Th*₂` without an additional “preserves-Th*” axiom.
  Convenience: the same hypothesis set is packaged as `Th*TransportAssumptions` with theorem `preserves-Th*-from-Flowᵃ`.

## Representational truth (ports/adapters)

The “presentation-independent” API uses satisfaction equivalence (↔) as the notion of sameness:

- Boundary I/O: `LogOS/Boundary/IO.agda` (`BoundaryIO`).
- Boundary ports: `LogOS/Boundary/Port.agda` (`BoundaryPort`) and interlingua translation:
  `LogOS/Ports/Semantic/Interlingua.agda`.

Statements of the form “X is preserved by translation” are usually **up to satisfaction** (a `↔`), not propositional `≡`.

Limit/stabilisation transport for presentations (Kleene `μ`) is also explicitly packaged:

- `LogOS/Ports/Semantic/Interoperability.agda` (`Limit.translate-μ≤`, `Limit.translate-μ≤↑`).
  These are satisfaction-level implications (`SatF₂↑`), not equalities, and require explicit ωCPO/continuity hypotheses.

Limit/stabilisation transport for *processes* is also explicitly packaged:

- `LogOS/Computation/ProcessLimit.agda` defines `run∞` (“execute for arbitrarily many steps from a given state”) as a Kleene `μ` in a slice preorder, together with a transport theorem `TransportLax.run∞-map≤` under explicit ωCPO/continuity assumptions.
- `LogOS/Computation/ProcessLimitSub2Cat.agda` packages the same story as a compositional interface: objects carry the `LimitData` needed to define `run∞`, and 1-cells carry the ω-continuity witness needed to preserve it (lemma `preserves-run∞`).

## 2-categorical bookkeeping (typed guardrail, no new axioms)

Several “refinement calculus” stories are packaged as thin 2-categories (`RelThin2Cat`, and the same-universe specialization `Thin2Cat`) so Agda can check:
- parallel morphisms can be compared (2-cells),
- whiskered, and
- composed.

This is a typing/structuring device; it does not add logical power.

Authoritative modules:
- `LogOS/Minimal/RelThin2Cat.agda` (thin 2-category interface over a two-level hom preorder).
- `LogOS/Minimal/Thin2Cat.agda` (same-universe specialization + laws as `≈`).
- `LogOS/Theorems/CategoryTheory/WrapperCore.agda` (`Ref2CatCore` and the conversions `RelThin2Cat→Ref2CatCore` / `Thin2Cat→Ref2CatCore`).
- Instances: kernels (`LogOS/Kernel/Hom2Cat.agda`), ports (`LogOS/Theorems/CategoryTheory/Port2Cat.agda`), presentations (`LogOS/Ports/Semantic/Presentation2Cat.agda`), processes (`LogOS/Computation/Process2Cat.agda`), and ωCPO maps (`LogOS/Theorems/Boundary/OmegaCPOMap2Cat.agda`).

## Meaningfulness / vacuity guards

Many kernels/models deliberately support “scaffold” instantiations where satisfaction is trivial (e.g. always true).
To prevent accidental over-interpretation, “meaningfulness” is expressed as explicit guards:

- Kernel guards: `LogOS/Boundary/KernelVacuityGuards.agda` (`KernelVacuityGuards`).
  These witnesses are **observational** (distinguishable by boundary satisfaction), not merely “by definition”.
- Port/adapter guards: `LogOS/Ports/Semantic/VacuityGuards.agda` (`PortVacuityGuards`, `AdapterVacuityGuards`).
- First-class non-triviality records (portable inputs to the guard spine): `LogOS/Ports/Semantic/Meaningful.agda`
  (`MeaningfulBoundaryIO`, `MeaningfulSatSystem`, and conversions to/from `VacuityGuards`).
- Prequantale/scale guards: `LogOS/QAdapters/Guards.agda` (`QAdapterVacuityGuards`).

Concrete sanity: `Tests/MeaningfulModels.agda` exhibits a tiny explicit model inhabiting these guards, showing they are
satisfiable and non-empty.
