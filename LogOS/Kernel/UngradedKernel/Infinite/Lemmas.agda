{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Infinite.Lemmas where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Infinite as Inf
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.UngradedKernel.Endo
open import LogOS.Kernel.UngradedKernel.Infinite
import LogOS.Kernel.InfiniteLemmasShared as SharedInf

-- Downstream-friendly facts for the “infinite kernel” companion structure.
--
-- These are the core metalogic lemmas you typically want everywhere:
--  - `Th⋆` as a limit (sup of approximants),
--  - μ-induction / least-pre-fixedpoint,
--  - equality at `Th⋆` from sandwich bounds (`id ≤ f ≤ Flow`),
--  - and simple corollaries for endomaps (Flow-close, etc.).

module For {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           (IK : InfiniteKernel Sig Q) where
  open InfiniteKernel IK using (K; po; ωCPO; FF)
  open UngradedKernel K using (BB; GTruth)

  private
    CP = BulkBoundary.bnd BB
    module CP = ConPreorder CP
    module I = Inf.For CP GTruth ωCPO FF

  Th⋆ : CP.Con
  Th⋆ = Th⋆K K

  module S =
    SharedInf.For
      CP
      Th⋆
      (Endo K)
      Endo.fn
      (_≤₂_ K)
      (λ le → le)
      (λ le → le)
      (idEndo K)
      (λ c → refl)
      _∘E_
      (λ g f c → refl)
      (Flow-Endo K)
      (Flow-closeEndo K)
      (f≤Flow→fTh⋆≤Th⋆ K)
      (Flow≤f→Th⋆≤fTh⋆ K)
      (id≤Flow-close K)
      (Flow-close≤Flow K)
      (Truth.GuardedCore.GuardedClosure.mono GTruth)
      (Truth.GuardedCore.GuardedClosure.idemp-lax GTruth)

  -- `Th⋆` really is a fixed point (as an equality) thanks to boundary antisymmetry.

  FlowTh⋆≡Th⋆∞ : Endo.fn (Flow-Endo K) Th⋆ ≡ Th⋆
  FlowTh⋆≡Th⋆∞ = I.FlowTh⋆≡Th⋆ (BulkBoundaryPO.po-bnd po)

  open I public
    using
      ( Th⋆-as-supω
      ; approxS
      ; approx-mono-step
      ; approx-mono
      ; approx-all→supω≤
      ; approx-all→Th⋆≤
      ; Th⋆≤Flow-fixed
      ; supω-mono
      ; StablePredicate
      ; stable-on-approximants→stable-on-Th⋆
      )
    renaming
      ( μ-induction  to μ-induction∂
      )

  -- Sandwich lemmas at Th⋆: key “closure step” facts.
  --
  -- Without antisymmetry you already get the two inequalities (useful when your
  -- set-level equality is mutual refinement).

  sandwich-bounds-at-Th⋆
    : (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → (CP._⊑_ Th⋆ (Endo.fn f Th⋆)) × (CP._⊑_ (Endo.fn f Th⋆) Th⋆)
  sandwich-bounds-at-Th⋆ = S.sandwich-bounds-at-Th⋆

  -- With antisymmetry (available in `InfiniteKernel.po`) you get equality at Th⋆.

  sandwich-fixed-at-Th⋆
    : (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → Endo.fn f Th⋆ ≡ Th⋆
  sandwich-fixed-at-Th⋆ f infl f≤tf =
    let
      open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
      p = S.sandwich-fixed-at-Th⋆ f infl f≤tf
    in
    antisym (≈CP⇒ {CP = CP} p) (≈CP⇐ {CP = CP} p)

  -- Handy corollaries for endomaps (mostly re-exports in a convenient shape).

  f≤Flow→fTh⋆≤Th⋆∞
    : (f : Endo K) → _≤₂_ K f (Flow-Endo K) → CP._⊑_ (Endo.fn f Th⋆) Th⋆
  f≤Flow→fTh⋆≤Th⋆∞ f le = f≤Flow→fTh⋆≤Th⋆ K f le

  Flow≤f→Th⋆≤fTh⋆∞
    : (f : Endo K) → _≤₂_ K (Flow-Endo K) f → CP._⊑_ Th⋆ (Endo.fn f Th⋆)
  Flow≤f→Th⋆≤fTh⋆∞ f le = Flow≤f→Th⋆≤fTh⋆ K f le

  -- Flow-close wrappers (common in closure-model code).

  Flow-close-fixed-at-Th⋆
    : (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → Endo.fn (Flow-closeEndo K f) Th⋆ ≡ Th⋆
  Flow-close-fixed-at-Th⋆ f infl f≤tf =
    let
      open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
      p = S.Flow-close-fixed-at-Th⋆ f infl f≤tf
    in
    antisym (≈CP⇒ {CP = CP} p) (≈CP⇐ {CP = CP} p)

  -- Sup monotonicity (derived from `least`): if f ≤ g pointwise then sup f ≤ sup g.
  -- (available via `LogOS.Minimal.Infinite`)

  -- Closure-step fixed point at Th⋆ (for the generic `ClosureStep` API in Endo).

  step-fixed-at-Th⋆ : (s : ClosureStep K) → Endo.fn (ClosureStep.endo s) Th⋆ ≡ Th⋆
  step-fixed-at-Th⋆ s =
    sandwich-fixed-at-Th⋆ (ClosureStep.endo s) (ClosureStep.infl s) (ClosureStep.leFlow s)

  -- Sandwich fusion (direct wrapper): compose two “closure steps” and get a Th⋆-fixed equality.

  sandwich-compose
    : (f g : Endo K)
    → _≤₂_ K (idEndo K) f → _≤₂_ K f (Flow-Endo K)
    → _≤₂_ K (idEndo K) g → _≤₂_ K g (Flow-Endo K)
    → Endo.fn (g ∘E f) Th⋆ ≡ Th⋆
  sandwich-compose f g inflf f≤flow inflg g≤flow =
    let
      open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
      p = S.sandwich-compose f g inflf f≤flow inflg g≤flow
    in
    antisym (≈CP⇒ {CP = CP} p) (≈CP⇐ {CP = CP} p)

  -- Stability-reflection schema (assumption record):
  -- if a predicate is (1) upward closed and (2) closed under ω-sups,
  -- then it holds at `Th⋆` whenever it holds on all approximants.

  -- (StablePredicate + reflection available via `LogOS.Minimal.Infinite`)
