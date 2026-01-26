{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Infinite.Lemmas where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Infinite as Inf
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Endo
open import LogOS.Kernel.Graded.Infinite

-- Downstream-friendly facts for the “infinite graded kernel” companion structure,
-- instantiated at the saturation grade.

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (IK : InfiniteGradedKernel Sig Q)
  where

  open InfiniteGradedKernel IK using (K; po; ωCPO; FF)
  open GradedKernel K using (BB; GTruth)

  private
    CP = BulkBoundary.bnd BB
    module CP = ConPreorder CP
    module GT∞ = Truth.GuardedCore
    GC = GT∞.forgetGradedClosure GTruth
    module I = Inf.For CP GC ωCPO FF

  Th⋆ : CP.Con
  Th⋆ = Th⋆K K

  -- `Th⋆` really is a fixed point (as an equality) thanks to boundary antisymmetry.

  FlowTh⋆≡Th⋆∞ : Endo.fn (Flow-Endo K) Th⋆ ≡ Th⋆
  FlowTh⋆≡Th⋆∞ = I.FlowTh⋆≡Th⋆ (BulkBoundaryPO.po-bnd po) -- ANTISYM-OK

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
      ( μ-induction to μ-induction∂
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
  sandwich-bounds-at-Th⋆ f infl f≤tf =
    let th≤fth = infl Th⋆
        fth≤tfth = f≤tf Th⋆
        tfth≤th = FlowTh⋆≤Th⋆ K
    in th≤fth , CP.trans fth≤tfth tfth≤th

  -- With antisymmetry (available in `InfiniteGradedKernel.po`) you get equality at Th⋆.

  sandwich-fixed-at-Th⋆
    : (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → Endo.fn f Th⋆ ≡ Th⋆
  sandwich-fixed-at-Th⋆ f infl f≤tf =
    let open BulkBoundaryPO po using (po-bnd) -- ANTISYM-OK
        open PartialOrder po-bnd using (antisym) -- ANTISYM-OK
        p = sandwich-bounds-at-Th⋆ f infl f≤tf
    in antisym (snd p) (fst p) -- ANTISYM-OK

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
    sandwich-fixed-at-Th⋆ (Flow-closeEndo K f)
      (id≤Flow-close K f infl)
      (Flow-close≤Flow K f f≤tf)

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
    sandwich-fixed-at-Th⋆ (g ∘E f)
      (λ c → CP.trans (inflf c) (inflg (Endo.fn f c)))
      (λ c →
        let step₁ = g≤flow (Endo.fn f c)           -- g(f c) ≤ Flow(f c)
            step₂ = Truth.GuardedCore.GuardedClosure.mono GC (f≤flow c)
            step₃ = Truth.GuardedCore.GuardedClosure.idemp-lax GC c
        in CP.trans step₁ (CP.trans step₂ step₃))
