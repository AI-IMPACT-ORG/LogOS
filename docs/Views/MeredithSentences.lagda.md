<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Meredith Sentences — LogicKernel / CHL (Ultra-Compact Core Math)

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
import LogOS.Kernel.Core as Core
open import LogOS.Kernel.LogicKernel as LK
import LogOS.Kernel.LogicKernel.BudgetedTier as LKBud
import LogOS.Theorems.Boundary.ContinuityCore as ContinuityCore
import LogOS.Theorems.Boundary.Stabilisation as Stabilisation

module MuFusion = Stabilisation.MuFusion

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
  where

  Code : Set ℓ
  Code = LK.LogicKernel.Code K

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (LK.LogicKernel.BB K)

  -- ------------------------------------------------------------------------
  -- Meredith anchors (LogicKernel interface, unpacked as named lemmas).
  --
  -- These are not extra axioms: each is definitional or a field/lemma in
  -- `LogOS/Kernel/LogicKernel.agda`.
  -- ------------------------------------------------------------------------

  Meredith₁-decode∘encode
    : ∀ c → LK.LogicKernel.decode K (LK.LogicKernel.encode K c) ≡ c
  Meredith₁-decode∘encode = LK.LogicKernel.decode∘encode K

  Meredith₂-reify-decode
    : ∀ γ → LK.LogicKernel.decode K (LK.LogicKernel.reify K γ) ≡ LK.LogicKernel.decode K γ
  Meredith₂-reify-decode = LK.LogicKernel.reify-decode K

  Meredith₃-body-decode
    : ∀ γ →
      LK.LogicKernel.decode K (LK.LogicKernel.Body K γ)
        ≡ LK.LogicKernel.Body∂ K (LK.LogicKernel.decode K γ)
  Meredith₃-body-decode = LK.LogicKernel.body-decode K

  Meredith₄-guard-decode
    : ∀ γ →
      LK.LogicKernel.decode K (LK.LogicKernel.Guard K γ)
        ≡ LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.step (LK.LogicKernel.G K))
            (LK.LogicKernel.decode K γ)
  Meredith₄-guard-decode = LK.LogicKernel.guard-decode K

  Meredith₅-γ*-flowcode-fixed
    : Core.Code≈ (LK.LogicKernel.shape K)
        (LK.LogicKernel.γ* K)
        (LK.FlowCode K (LK.LogicKernel.γ* K))
  Meredith₅-γ*-flowcode-fixed = LK.LogicKernel.γ*-guard K

  Meredith₆-decode-γ*
    : LK.LogicKernel.decode K (LK.LogicKernel.γ* K)
        ≡ LK.GTier.Th* (LK.LogicKernel.G K)
  Meredith₆-decode-γ* = LK.LogicKernel.decode-γ* K

  Meredith₇-Th*-fixed
    : (ConPreorder._⊑_ CP
        (LK.GTier.Th* (LK.LogicKernel.G K))
        (LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.sat (LK.LogicKernel.G K))
          (LK.GTier.Th* (LK.LogicKernel.G K))))
      ×
      (ConPreorder._⊑_ CP
        (LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.sat (LK.LogicKernel.G K))
          (LK.GTier.Th* (LK.LogicKernel.G K)))
        (LK.GTier.Th* (LK.LogicKernel.G K)))
  Meredith₇-Th*-fixed = LK.GTier.Th*-fixed (LK.LogicKernel.G K)

  Meredith₇-infl-sat
    : ∀ c →
      ConPreorder._⊑_ CP
        c
        (LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.sat (LK.LogicKernel.G K)) c)
  Meredith₇-infl-sat = LK.GTier.infl-sat (LK.LogicKernel.G K)

  Meredith₇-idemp-sat
    : ∀ c →
      ConPreorder._⊑_ CP
        (LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.sat (LK.LogicKernel.G K))
          (LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.sat (LK.LogicKernel.G K)) c))
        (LK.GTier.Flow (LK.LogicKernel.G K) (LK.GTier.sat (LK.LogicKernel.G K)) c)
  Meredith₇-idemp-sat = LK.GTier.idemp-sat (LK.LogicKernel.G K)

  -- CHL-facing operational anchor: raw step agrees (up to mutual refinement) with
  -- “compute then stabilise at the step grade”.
  Meredith₈-flowCode≈boxAt-step-body
    : ∀ γ →
      Core.Code≈ (LK.LogicKernel.shape K)
        (LK.FlowCode K γ)
        (LK.BoxAt K (LK.GTier.step (LK.LogicKernel.G K)) (LK.LogicKernel.Body K γ))
  Meredith₈-flowCode≈boxAt-step-body = LK.flowCode≈BoxAt-step-body K

  -- ------------------------------------------------------------------------
  -- Budgeted/resource view anchors (optional strengthening; no new axioms).
  -- ------------------------------------------------------------------------

  module Resource (BT : LKBud.BudgetedTier K) where
    module D = LKBud.Derived K BT
    open LKBud.BudgetedTier BT

    boxAt-mono-grade
      : ∀ {g g'}
      → _≤g_ g g'
      → (γ : Code)
      → Core.Code≤ (LK.LogicKernel.shape K) (LK.BoxAt K g γ) (LK.BoxAt K g' γ)
    boxAt-mono-grade = D.boxAt-mono-grade

    boxAt-comp-lax
      : ∀ g g' (γ : Code)
      → Core.Code≤ (LK.LogicKernel.shape K)
          (LK.BoxAt K g' (LK.BoxAt K g γ))
          (LK.BoxAt K (_·g_ g g') γ)
    boxAt-comp-lax = D.boxAt-comp-lax

    boxAt≤Box
      : ∀ g (γ : Code)
      → Core.Code≤ (LK.LogicKernel.shape K) (LK.BoxAt K g γ) (LK.Box K γ)
    boxAt≤Box = D.boxAt≤Box

  -- ------------------------------------------------------------------------
  -- μ-level stabilization anchors (M₉–M₁₀ in the prose).
  -- ------------------------------------------------------------------------

  private
    module GC = Truth.GuardedCore {ℓ = ℓ}
    open ConPreorder CP using (Con; _⊑_)

    satK : LK.GTier.Step (LK.LogicKernel.G K)
    satK = LK.GTier.sat (LK.LogicKernel.G K)

    FlowSat : Con → Con
    FlowSat = LK.GTier.Flow (LK.LogicKernel.G K) satK

    monoSat : ∀ {c c'} → _⊑_ c c' → _⊑_ (FlowSat c) (FlowSat c')
    monoSat le =
      LK.GTier.mono (LK.LogicKernel.G K) {g = satK} le

    GCsat : GC.GuardedClosure CP
    GCsat =
      record
        { Flow      = FlowSat
        ; mono      = monoSat
        ; infl      = LK.GTier.infl-sat (LK.LogicKernel.G K)
        ; idemp-lax = LK.GTier.idemp-sat (LK.LogicKernel.G K)
        ; Th*       = LK.GTier.Th* (LK.LogicKernel.G K)
        ; Th*-fixed = LK.GTier.Th*-fixed (LK.LogicKernel.G K)
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

Fix `K : LogicKernel Sig Q` (`LogOS/Kernel/LogicKernel.agda`).

Notation (barebones)
--------------------
- `γ, δ : Code` and `c, d : Con` (boundary constraints).
- `γ ⊢ δ` = code refinement; `γ ≈ δ` = mutual refinement.
- `c ⊑ d` = boundary refinement; `c ≈ d` = mutual refinement on the boundary preorder (`_≈CP_`).
- `⟦γ⟧ := decode γ` and `η c := encode c`.
- `ρ γ := reify γ` (safe self-reflection; observationally inert).
- `B := Body`, `B∂ := Body∂`, `▹ := Guard`.
- `FlowCode γ := ▹ (B γ)`  (raw operational step).
- `g : Step` (step index; becomes a budget/resource when `BudgetedTier` is assumed),
  `Flow₍g₎ : Con → Con`, `□₍g₎ γ := η (Flow₍g₎ ⟦γ⟧)`.
  When `K` comes from a graded kernel, `Step` is the resource scale `Scale` of `Q`
  (`QAdapter`), with order `≤` and multiplication `·` (`LogOS/Kernel/LogicKernel/BudgetedTier.agda`).
- `□ γ := □₍sat₎ γ`, `★ := γ*`, `Θ := Th*`.
- `μ F` = Kleene μ (ω-sup of iterates from `⊥`, when `OmegaCPO` is assumed).

Reading note (guardrail): (M₁–M₇) are kernel fields/lemmas re-exported by this
module (the `Quotes` section above).
(M₈) is a derived coherence lemma (“compute then stabilise at the step grade”).
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
If you assume a `BudgetedTier K` (`LogOS/Kernel/LogicKernel/BudgetedTier.agda`):
- (R₁a) `g ≤ h ⇒ □₍g₎ γ ⊢ □₍h₎ γ`
- (R₁b) `□₍h₎ (□₍g₎ γ) ⊢ □₍g·h₎ γ`  (apply `g` then `h`)
- (R₁c) `□₍g₎ γ ⊢ □γ`  (since `sat` is top)

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
