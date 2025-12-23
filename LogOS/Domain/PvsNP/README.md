<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

P vs NP — Core
==============

What this is / isn't
--------------------
- Not a ZFC proof of classical P≠NP.
- Conditional: if the stated assumptions hold in a model, the separation claim follows.
- Generic route: the graded-flow interface (`DetPolyTimeBoundedG` / `PolyWitnessedTotalVerificationG`) is P/NP-shaped, not language-relative NP.
- Classical alignment is explicit and separate (via `TruthRoute` + `ClassicalPvsNP`).

Core
----
- Recommended stable surface: `LogOS/Models/Complexity/Core.agda` (namespace `PvsNP` / `PvsNPFromInfo_Grade_Only` / `ClassicalPvsNP`).
  Safe P/NP-only surface: `LogOS/Models/Complexity/PvsNP/Public.agda`.
  The core bundle lives under `LogOS/Domain/Complexity/*`:
  - `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` — core GRH‑aligned ledger for proof‑search vs verification.
  - `LogOS/Domain/Complexity/Model.agda` — standard complexity model scaffold.
  - `LogOS/Domain/Complexity/PvsNPFromInfo_Grade_Only.agda` — canonical minimal route (DetBottleneck + InfoHardness → PvsNPClaim).
    ℕ predicates can be lifted via `PvsNPFromInfo_Grade_Only.FromNat` / `PolyGrade.FromNat`.
  - `LogOS/Domain/Complexity/PvsNP.agda` — language-relative P vs NP claim pack; `mkPack` rewraps `InNP` + `¬ InP` (no derivation).
  - `LogOS/Domain/Complexity/ClassicalPvsNP.agda` — literature-aligned P/NP interface (cost = time) with a bridge from `TruthRoute`.
  - `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda` — grade-native P/NP-shaped interface (canonical).
  - `LogOS/Domain/Complexity/ProofSearchOpacitySpine.agda` — proof-search opacity spine (shared core with GRH/opacity);
    general budgets via `ProofSearchOpacitySpine.For.Budgeted.GeneralB`,
    decode-ext budgets via `ProofSearchOpacitySpine.For.BudgetBy`,
    non-vacuity guard via `ProofSearchOpacitySpine.For.VacuityGuards`.
- Concrete polynomial/time plumbing lives under `LogOS/Domain/Complexity/Poly.agda`
  (grade-native predicate: `LogOS/Domain/Complexity/PolyGrade.agda`;
  arithmetic helpers in `LogOS/Domain/Complexity/Arithmetic.agda`).

Instantiations
--------------
- Domain models import `LogOS.Models.Complexity.Core` and supply `Assumptions` locally
  (NP witness + bottleneck + info-hardness).
- Grade-native variants live under `PvsNPFromInfo_Grade_Only.For.WithAcc` and use `PolyGrade` (`PolyPredG`).
- Operator-style witnesses typically come from `LogOS/Domain/Universality/*` (analytic bounds).
  - The classical surface is available as `LogOS.Models.Complexity.Core.ClassicalPvsNP`.

Build
-----
- Core tests + publication docs: `make ci` (from `agda_library_1.0/`)

Notes
-----
- All P≠NP statements here are explicitly conditional on separation assumptions (e.g. `SpectralSeparationAssumptions` / `SpectralSeparationAssumptionsW`). This keeps the core precise and reusable. Meta/meta note: see `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` for the spectral separation aliases (`SpectralSeparationOutput`, `HasSeparation`, `NoSeparation`) and the diagonal witness showing any reflective system must leave some code in the undefined branch—so spectral separation remains a partial, model-supplied artifact rather than a total internal inference.

Start here
----------
- Model scaffold: `LogOS/Domain/Complexity/Model.agda`
- Conditional separation pack: `LogOS/Domain/Complexity/PvsNP_Grade_Only.agda`
- Polynomial predicate/tooling: `LogOS/Domain/Complexity/Poly.agda`
