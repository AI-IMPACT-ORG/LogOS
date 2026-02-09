<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — Meredith Sentences (Kernel / CHL Core)

```agda
{-# OPTIONS --safe #-}
module docs.Views.MeredithSentences where

-- Typechecked “view surface” for the Meredith-sentence documentation.
--
-- This module only anchors the referenced kernel laws/identifiers so doc builds
-- fail if names move or coherence facts change.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder ; BulkBoundary ; _≈CP_)
import LogOS.Minimal.Truth as Truth
import LogOS.API.Kernel as Kernels
import LogOS.API.Strengthenings as Strengthenings

module Shape = Kernels.Shape
module LK = Kernels
module Stabilisation = Strengthenings.Stabilisation
module ContinuityCore = Strengthenings.Stabilisation.ContinuityCore

module MuFusion = Stabilisation.MuFusion

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.Kernel Sig Q)
  where

  Code : Set ℓ
  Code = LK.Kernel.Code K

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (LK.Kernel.BB K)

  -- ------------------------------------------------------------------------
  -- Meredith anchors (Kernel interface, unpacked as named lemmas).
  --
  -- These are not extra axioms: each is a field/lemma (often `refl` after
  -- unfolding the canonical bridges) in
  -- `LogOS/Kernel.agda`.
  -- ------------------------------------------------------------------------

  Meredith₁-decode∘encode
    : ∀ c → LK.Kernel.decode K (LK.Kernel.encode K c) ≡ c
  Meredith₁-decode∘encode = LK.Kernel.decode∘encode K

  Meredith₂-reify-decode
    : ∀ γ → LK.Kernel.decode K (LK.Kernel.reify K γ) ≡ LK.Kernel.decode K γ
  Meredith₂-reify-decode = LK.Kernel.reify-decode K

  Meredith₃-body-decode
    : ∀ γ →
      LK.Kernel.decode K (LK.Kernel.Body K γ)
        ≡ LK.Kernel.Body∂ K (LK.Kernel.decode K γ)
  Meredith₃-body-decode = LK.Kernel.body-decode K

  Meredith₄-guard-decode
    : ∀ γ →
      LK.Kernel.decode K (LK.Kernel.Guard K γ)
        ≡ LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.step (LK.Kernel.G K))
            (LK.Kernel.decode K γ)
  Meredith₄-guard-decode = LK.Kernel.guard-decode K

  Meredith₅-γ*-flowcode-fixed
    : Shape.Code≈ (LK.Kernel.shape K)
        (LK.Kernel.γ* K)
        (LK.FlowCode K (LK.Kernel.γ* K))
  Meredith₅-γ*-flowcode-fixed = LK.Kernel.γ*-guard K

  Meredith₆-decode-γ*
    : LK.Kernel.decode K (LK.Kernel.γ* K)
        ≡ LK.GTier.Th* (LK.Kernel.G K)
  Meredith₆-decode-γ* = LK.Kernel.decode-γ* K

  Meredith₇-Th*-fixed
    : (ConPreorder._⊑_ CP
        (LK.GTier.Th* (LK.Kernel.G K))
        (LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.sat (LK.Kernel.G K))
          (LK.GTier.Th* (LK.Kernel.G K))))
      ×
      (ConPreorder._⊑_ CP
        (LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.sat (LK.Kernel.G K))
          (LK.GTier.Th* (LK.Kernel.G K)))
        (LK.GTier.Th* (LK.Kernel.G K)))
  Meredith₇-Th*-fixed = LK.GTier.Th*-fixed (LK.Kernel.G K)

  Meredith₇-infl-sat
    : ∀ c →
      ConPreorder._⊑_ CP
        c
        (LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.sat (LK.Kernel.G K)) c)
  Meredith₇-infl-sat = LK.GTier.infl-sat (LK.Kernel.G K)

  Meredith₇-idemp-sat
    : ∀ c →
      ConPreorder._⊑_ CP
        (LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.sat (LK.Kernel.G K))
          (LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.sat (LK.Kernel.G K)) c))
        (LK.GTier.Flow (LK.Kernel.G K) (LK.GTier.sat (LK.Kernel.G K)) c)
  Meredith₇-idemp-sat = LK.GTier.idemp-sat (LK.Kernel.G K)

  -- CHL-facing operational anchor: raw step agrees (up to mutual refinement) with
  -- “compute-then-stabilise at the step grade”.
  Meredith₈-flowCode≈boxAt-step-body
    : ∀ γ →
      Shape.Code≈ (LK.Kernel.shape K)
        (LK.FlowCode K γ)
        (LK.BoxAt K (LK.GTier.step (LK.Kernel.G K)) (LK.Kernel.Body K γ))
  Meredith₈-flowCode≈boxAt-step-body = LK.flowCode≈BoxAt-step-body K

  -- ------------------------------------------------------------------------
  -- Budgeted/resource view anchors (optional strengthening; no new axioms).
  -- ------------------------------------------------------------------------

  module Resource (BT : LK.BudgetedTier K) where
    module D = LK.Derived K BT
    open LK.BudgetedTier BT

    boxAt-mono-grade
      : ∀ {g g'}
      → _≤g_ g g'
      → (γ : Code)
      → Shape.Code≤ (LK.Kernel.shape K) (LK.BoxAt K g γ) (LK.BoxAt K g' γ)
    boxAt-mono-grade = D.boxAt-mono-grade

    boxAt-comp-lax
      : ∀ g g' (γ : Code)
      → Shape.Code≤ (LK.Kernel.shape K)
          (LK.BoxAt K g' (LK.BoxAt K g γ))
          (LK.BoxAt K (_·g_ g g') γ)
    boxAt-comp-lax = D.boxAt-comp-lax

    boxAt≤Box
      : ∀ g (γ : Code)
      → Shape.Code≤ (LK.Kernel.shape K) (LK.BoxAt K g γ) (LK.Box K γ)
    boxAt≤Box = D.boxAt≤Box

  -- ------------------------------------------------------------------------
  -- μ-level stabilisation anchors (M₉–M₁₀ in the prose).
  -- ------------------------------------------------------------------------

  private
    module GC = Truth.GuardedCore {ℓ = ℓ}
    open ConPreorder CP using (Con; _⊑_)

    satK : LK.GTier.Step (LK.Kernel.G K)
    satK = LK.GTier.sat (LK.Kernel.G K)

    FlowSat : Con → Con
    FlowSat = LK.GTier.Flow (LK.Kernel.G K) satK

    monoSat : ∀ {c c'} → _⊑_ c c' → _⊑_ (FlowSat c) (FlowSat c')
    monoSat le =
      LK.GTier.mono (LK.Kernel.G K) {g = satK} le

    GCsat : GC.GuardedClosure CP
    GCsat =
      record
        { Flow      = FlowSat
        ; mono      = monoSat
        ; infl      = LK.GTier.infl-sat (LK.Kernel.G K)
        ; idemp-lax = LK.GTier.idemp-sat (LK.Kernel.G K)
        ; Th*       = LK.GTier.Th* (LK.Kernel.G K)
        ; Th*-fixed = LK.GTier.Th*-fixed (LK.Kernel.G K)
        }

    module C = ContinuityCore.For CP GCsat

  Meredith₉-Th*≈μFlow
    : (ωCPO : GC.OmegaCPO CP)
      (FF   : GC.FiniteFirst CP GCsat ωCPO)
    → _≈CP_ CP (GC.GuardedClosure.Th* GCsat) (C.μFlow ωCPO)
  Meredith₉-Th*≈μFlow ωCPO FF = C.Th*≈μFlow ωCPO FF

  module Meredith₁₀-Transport
    {ℓ₂ : Level}
    (CP₂ : ConPreorder ℓ₂)
    (G₂  : (let module GC₂ = Truth.GuardedCore {ℓ = ℓ₂} in GC₂.GuardedClosure CP₂))
    where

    private
      module GC₂ = Truth.GuardedCore {ℓ = ℓ₂}
      module MF = MuFusion.For CP CP₂

    preserves-Th*-from-Flow
      : (ω₁ : GC.OmegaCPO CP)
        (ω₂ : GC₂.OmegaCPO CP₂)
        {map : ConPreorder.Con CP → ConPreorder.Con CP₂}
        (M   : MF.OmegaCPOMap ω₁ ω₂ map)
        (FF₁ : GC.FiniteFirst CP GCsat ω₁)
        (FF₂ : GC₂.FiniteFirst CP₂ G₂ ω₂)
        (comm : ∀ c →
          ConPreorder._⊑_ CP₂
            (map (GC.GuardedClosure.Flow GCsat c))
            (GC₂.GuardedClosure.Flow G₂ (map c)))
      → ConPreorder._⊑_ CP₂ (map (GC.GuardedClosure.Th* GCsat)) (GC₂.GuardedClosure.Th* G₂)
    preserves-Th*-from-Flow ω₁ ω₂ M FF₁ FF₂ comm =
      MF.preserves-Th*-from-Flow M GCsat G₂ FF₁ FF₂ comm
```

Purpose
-------
Fix `K : Kernel Sig Q` (`LogOS/Kernel.agda`). This view presents
the CHL-facing kernel as a compact “axiom poem”: a small list of named equations
and refinements that pin down the core interface (decode/encode, reflection,
guard/body, closure, and the distinguished stable witness).

Interpretation (analogy):
this document is a derived presentation (“view”) over the CHL-facing `Kernel`;
it does not add logical power.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Scope (formal)
--------------
- Parameter: `Kernel Sig Q`.

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| “Axiom poem” / compact interface axioms | (M₁–M₈) anchors in `Kernel` | Not additional axioms: each line is a field/lemma (often `refl` after unfolding canonical bridges). |
| Closure/modality □ | `Flow` / `BoxAt` / `Box` | In graded form: `BoxAt g γ := encode (Flow g (decode γ))`. `Box` is the ungraded/saturation instance. |
| Stable truth / fixed point invariant | `Th*`, `γ*` | `Th*` is a distinguished lax fixed-point witness; μ-characterisation is optional. |
| Kleene μ / least pre-fixed point | `μ` (when `OmegaCPO` + `FiniteFirst`) | Limit semantics is explicit and hypothesis-driven. |
| Resource/prequantale indexing | `BudgetedTier` (grades `g`) | Purely an optional view: it does not add logical power to the core. |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital prequantale in the finite-join sense (not complete); used via the graded/budgeted tier. |

Concretely, the resource view is anchored by `boxAt-mono-grade` and `boxAt-comp-lax`: grade monotonicity and lax compositionality of `BoxAt`.

Core definitions (literature style)
-----------------------------------

**Definition (Meredith anchor).** Each “Meredith sentence” in this file is a
field/lemma of `Kernel` (or a definitional consequence of that interface),
presented with a conventional symbolic spelling (`⟦_⟧`, `η`, `□`, …) and an exact
Agda anchor name (`Meredith₁`–`Meredith₈` above).

Assumptions (explicit)
----------------------
- (M₁–M₈) are kernel fields/lemmas (no extra hypotheses).
- (M₉–M₁₀) require explicit ωCPO/continuity hypotheses, as stated.
- The resource spelling requires `BudgetedTier K` (it is not part of the minimal kernel).

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: a compact “axiom poem” presentation (Meredith‑style) of a logical interface, with explicit anchors into the mechanized kernel fields.
- Weaker/lax by default: no hidden proof-irrelevance/antisymmetry; stability is expressed up to refinement/mutual refinement, not as judgmental equalities.
- Added by ports/adapters: code/reflection (`encode`/`decode`/`reify`) and compute‑then‑stabilise anchors make the CHL-facing kernel story interoperable across presentations.
- Assumption-scoped: μ/limit and resource/budget strengthenings are separate, explicitly‑hypothesized layers (ωCPO/continuity, `BudgetedTier`).

Theorem spine (authoritative)
-----------------------------
- Kernel core laws: `LogOS/Kernel.agda` (the anchored `Meredith₁`–`Meredith₈` fields/lemmas above).
- Resource/budget view (optional): `LogOS/Kernel/BudgetedTier.agda`.
- μ/least-pre-fixed-point characterisation (optional): `LogOS/Theorems/Boundary/ContinuityCore.agda` (`Th*≈μFlow`).
- μ-fusion transport (optional): `LogOS/Theorems/Boundary/MuFusion.agda` (`preserves-Th*-from-Flow`).
- The prose below is explanatory; the Agda anchors above are the authoritative claims.

Notation (barebones)
--------------------
- `γ, δ : Code` and `c, d : Con` (boundary constraints).
- `γ ⊢ δ` = code refinement; `γ ≈ δ` = mutual refinement.
- `c ⊑ d` = boundary refinement; `c ≈ d` = mutual refinement on the boundary preorder (`_≈CP_`).
- `⟦γ⟧ := decode γ` and `η c := encode c`.
- `ρ γ := reify γ` (safe self-reflection; observationally inert).
- `B := Body`, `B∂ := Body∂`, `▹ := Guard`.
- `FlowCode γ := ▹ (B γ)`  (raw operational step).
- `g : Step` (step index). Canonical bridges: from `Kernel`, `Step = ⊤` (no nontrivial budgets);
  from `GradedKernel`, `Step = QAdapter.Scale Q` (`LogOS/Kernel/FromUngradedKernel.agda`,
  `LogOS/Kernel/FromGradedKernel.agda`).
  `Flow₍g₎ : Con → Con`, `□₍g₎ γ := η (Flow₍g₎ ⟦γ⟧)`.
  A `BudgetedTier K` equips `Step` with an order `≤g` and multiplication `·g` (plus `sat-top`,
  monotonicity, and lax composition). Canonical instances are provided in
  `LogOS/Kernel/BudgetedTier.agda` (`budgetedTierFromUngradedKernel`, `budgetedTierFromGradedKernel`).
- `□ γ := □₍sat₎ γ`, `★ := γ*`, `Θ := Th*`.
- `μ F` = Kleene μ (ω-sup of iterates from `⊥`, when `OmegaCPO` is assumed).
  (Disambiguation: this is unrelated to the notation `ClosureOp.Notation.μ` for “monad multiplication”
  of a closure operator; see `LogOS/Minimal/Closure.agda`.)

Reading note (guardrail): (M₁–M₇) are kernel fields/lemmas re-exported by this
module (the `Quotes` section above).
(M₈) is a derived coherence lemma (“compute-then-stabilise at the step grade”).
(M₉–M₁₀) are limit-level strengthenings and require the stated ωCPO/continuity
hypotheses.

Meredith sentences (core)
-------------------------
- (M₁) `⟦η c⟧ ≡ c`
- (M₂) `⟦ρ γ⟧ ≡ ⟦γ⟧`
- (M₃) `⟦B γ⟧ ≡ B∂ ⟦γ⟧`
- (M₄) `⟦▹ γ⟧ ≡ Flow₍step₎ ⟦γ⟧`
- (M₅) `★ ≈ FlowCode ★`
- (M₆) `⟦★⟧ ≡ Θ`
- (M₇) `c ⊑ Flow₍sat₎ c` and `Flow₍sat₎ (Flow₍sat₎ c) ⊑ Flow₍sat₎ c`, and `Θ ⊑ Flow₍sat₎ Θ` and `Flow₍sat₎ Θ ⊑ Θ`
- (M₈) `FlowCode γ ≈ □₍step₎ (B γ)`

Meredith sentences (resource spelling, optional)
------------------------------------------------
If you assume a `BudgetedTier K` (`LogOS/Kernel/BudgetedTier.agda`):
- (R₁a) `g ≤ h ⇒ □₍g₎ γ ⊢ □₍h₎ γ`
- (R₁b) `□₍h₎ (□₍g₎ γ) ⊢ □₍g·h₎ γ`  (apply `g` then `h`)
- (R₁c) `□₍g₎ γ ⊢ □γ`  (by `BudgetedTier.sat-top`)

Meredith sentences (limit semantics, explicit hypotheses)
---------------------------------------------------------
- (M₉) If the boundary preorder has `OmegaCPO` and the saturation flow has `FiniteFirst`:
  `Θ ≈ μ (Flow₍sat₎)` (`LogOS/Theorems/Boundary/ContinuityCore.agda`).
- (M₁₀) If both sides have `OmegaCPO`+`FiniteFirst` (so (M₉) applies) and `map` is
  an `OmegaCPOMap` and commutes laxly with flow:
  `map Θ₁ ⊑ Θ₂` (`LogOS/Theorems/Boundary/MuFusion.agda`).

These hypothesis sets are available as explicit bundles:
- `ContinuityCore.For.MuData` (ωCPO + finite-first approximants for one closure), and
- `MuFusion.For.Th*TransportAssumptions` (adds ω-continuity of `map` and lax flow commutation).

Typechecked anchor surface: this document (`docs/Views/MeredithSentences.lagda.md`).

Pointers (no repetition)
------------------------
- Kernel field map and tier glossary: `docs/LogOS_Core_Spec.lagda.md`.
- μ/limit facts and hypotheses: `docs/Terminology.lagda.md` and `docs/Kernel/ClaimRegister.lagda.md`.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`
- Observer semantics (physics-of-information interpretation): `docs/Views/ObserverSemantics.lagda.md`
- Controlled feedback (budgeted stabilisation): `docs/Views/ControlledFeedback.lagda.md`
