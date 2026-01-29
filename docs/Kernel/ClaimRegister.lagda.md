<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Kernel Claim Register (Literal vs Stabilisation vs Representational)

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

open import LogOS.Kernel.LogicKernel using (LogicKernel; Box; Th*)

import LogOS.Kernel.LogicKernel.VacuityGuards as KVac
import LogOS.Ports.Semantic.VacuityGuards as PVac
import LogOS.QAdapters.Guards as QVac

import LogOS.Ports.Semantic.Interoperability as Interoperability
import LogOS.Theorems.Boundary.Stabilisation as Stabilisation

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
  (m  : SatMor Ctx₁ (ConPreorder.Con CP₁) Sat₁ Ctx₂ (ConPreorder.Con CP₂) Sat₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ (ConPreorder.Con CP₁) Sat₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ (ConPreorder.Con CP₂) Sat₂)
  where
  module Limit = Interoperability.Limit CP₁ CP₂ m P₁ P₂
  translate-μ≤-exists : _
  translate-μ≤-exists = Limit.translate-μ≤
  translate-μ≤↑-exists : _
  translate-μ≤↑-exists = Limit.translate-μ≤↑

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : LogicKernel Sig Q) where
  box-exists : _
  box-exists = Box K
  th*-exists : _
  th*-exists = Th* (LogicKernel.G K)

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
- **Truth after stabilisation (closure):** a closure/fixed-point style statement (e.g. `Th*`, `Box`, Kleene `μ Flow`).
  By default, these are only *lax* fixed points (two inequalities), unless extra domain structure is assumed.
- **Representational truth (presentation):** a statement transported through ports/adapters (satisfaction equivalences),
  not judgmental equality of syntax/terms.
- **Analogy / interpretation:** explanatory metaphors; they never add logical power.

Notation (used throughout the docs): `≡` is propositional equality, `c ⊑ d` is (directed) refinement in a preorder,
`c ≈ d` is mutual refinement (two inequalities), and `P ↔ Q` is a satisfaction equivalence (paired implications).

This page is a compact “claim register”: it points to the **exact code surfaces**
that define what each phrase means.

## Kernel objects (literal)

- **Kernel shape:** `LogOS/Kernel/Core.agda` (`KernelShape`).
  This is the “shared” interface: S/H truth, boundary constraints, and reflective code (`encode`/`decode`).
- **LogicKernel:** `LogOS/Kernel/LogicKernel.agda` (`LogicKernel`).
  This repackages a kernel shape together with a parameterised guarded tier (`GTier`) so the same interface covers
  ungraded and graded kernels uniformly.

## Truth after stabilisation (closure; lax by default)

- **Operational code step:** `LogOS/Kernel/Core.agda` (`FlowCode`) and `LogOS/Kernel/LogicKernel.agda` (`FlowCode`).
  This is the one-step update on code (`Guard ∘ Body`).
- **Closure modality:** `LogOS/Kernel/LogicKernel.agda` (`BoxAt`, `Box`).
  These are *code-level* modalities defined by `encode ∘ Flow ∘ decode`.
- **Distinguished “stable truth”:** `LogOS/Kernel/LogicKernel.agda` (`GTier.Th*` / `Th*`).
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

The “presentation-independent” API uses satisfaction equivalence as the notion of sameness:

- Boundary I/O: `LogOS/Boundary/IO.agda` (`BoundaryIO`).
- Boundary ports: `LogOS/Boundary/Port.agda` (`BoundaryPort`) and interlingua translation:
  `LogOS/Ports/Semantic/Interlingua.agda`.

Statements of the form “X is preserved by translation” are usually **up to satisfaction** (a `↔`), not propositional `≡`.

Limit/stabilisation transport for presentations (Kleene `μ`) is also explicitly packaged:

- `LogOS/Ports/Semantic/Interoperability.agda` (`Limit.translate-μ≤`, `Limit.translate-μ≤↑`).
  These are satisfaction-level implications (`SatF₂↑`), not equalities, and require explicit ωCPO/continuity hypotheses.

## Meaningfulness / vacuity guards

Many kernels/models deliberately support “scaffold” instantiations where satisfaction is trivial (e.g. always true).
To prevent accidental over-interpretation, “meaningfulness” is expressed as explicit guards:

- Kernel guards: `LogOS/Kernel/LogicKernel/VacuityGuards.agda` (`KernelVacuityGuards`).
  These witnesses are **observational** (distinguishable by boundary satisfaction), not merely “by definition”.
- Port/adapter guards: `LogOS/Ports/Semantic/VacuityGuards.agda` (`PortVacuityGuards`, `AdapterVacuityGuards`).
- Quantale/scale guards: `LogOS/QAdapters/Guards.agda` (`QAdapterVacuityGuards`).

Concrete sanity: `Tests/MeaningfulModels.agda` exhibits a tiny explicit model inhabiting these guards, showing they are
satisfiable and non-empty.
