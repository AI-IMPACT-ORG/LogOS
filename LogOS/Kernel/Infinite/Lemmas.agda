{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Infinite.Lemmas where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Kernel.Infinite
open import Data.Ordinal as Ord

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
  open Kernel K using (BB; GTruth)

  private
    CP = BulkBoundary.bnd BB
    module CP = ConPoset CP
    module GT∞ = Truth.GuardedTruth Sig Q
    open GT∞

  Th⋆ : CP.Con
  Th⋆ = Th⋆K K

  -- `Th⋆` really is a fixed point (as an equality) thanks to boundary antisymmetry.

  FlowTh⋆≡Th⋆∞ : Endo.fn (Flow-Endo K) Th⋆ ≡ Th⋆
  FlowTh⋆≡Th⋆∞ = FlowTh⋆≡Th⋆ K po

  -- Unpack the “Th⋆ is a sup of approximants” data.

  approxS : ℕ → CP.Con
  approxS = FiniteFirst.approxS FF

  -- Approximants are an increasing ω-chain.

  approx-mono-step
    : ∀ n → CP._⊑_ (approxS n) (approxS (suc n))
  approx-mono-step n =
    let open GT∞.GuardedClosure (Kernel.GTruth K) renaming (Flow to F; infl to inflF)
        stepEq = FiniteFirst.step FF n
    in subst (λ x → CP._⊑_ (approxS n) x) (sym stepEq) (inflF (approxS n))

  approx-mono
    : ∀ {m n} → Ord._≤ℕ_ m n → CP._⊑_ (approxS m) (approxS n)
  approx-mono {m} {n} Ord.z≤n =
    subst (λ x → CP._⊑_ x (approxS n)) (sym (FiniteFirst.base FF))
      (OmegaCPO.isBot ωCPO (approxS n))
  approx-mono {m = suc m} {n = suc n} (Ord.s≤s mn) =
    let open GT∞.GuardedClosure (Kernel.GTruth K) renaming (Flow to F; mono to monoF)
        eqL = FiniteFirst.step FF m
        eqR = FiniteFirst.step FF n
        leF = monoF (approx-mono {m = m} {n = n} mn)     -- F(A m) ⊑ F(A n)
        leR = subst (λ y → CP._⊑_ (F (approxS m)) y) (sym eqR) leF
    in subst (λ x → CP._⊑_ x (approxS (suc n))) (sym eqL) leR

  Th⋆-as-supω
    : CP._⊑_ Th⋆ (OmegaCPO.supω ωCPO approxS)
      × CP._⊑_ (OmegaCPO.supω ωCPO approxS) Th⋆
  Th⋆-as-supω = FiniteFirst.Th⋆-as-sup FF

  -- Approximation principle: to bound `Th⋆`, it suffices to bound all approximants.

  approx-all→supω≤
    : (c : CP.Con)
    → (∀ n → CP._⊑_ (approxS n) c)
    → CP._⊑_ (OmegaCPO.supω ωCPO approxS) c
  approx-all→supω≤ c ub = OmegaCPO.least ωCPO approxS c ub

  approx-all→Th⋆≤
    : (c : CP.Con)
    → (∀ n → CP._⊑_ (approxS n) c)
    → CP._⊑_ Th⋆ c
  approx-all→Th⋆≤ c ub =
    let th≤sup = fst Th⋆-as-supω
        sup≤c  = approx-all→supω≤ c ub
    in CP.trans th≤sup sup≤c

  -- μ-induction at the kernel boundary: any Flow-pre-fixed point upper-bounds Th⋆.

  μ-induction∂
    : (c : CP.Con)
    → CP._⊑_ (Endo.fn (Flow-Endo K) c) c
    → CP._⊑_ Th⋆ c
  μ-induction∂ c pre =
    GT∞.μ-induction (Kernel.GTruth K) ωCPO FF c pre

  -- Corollary: if Flow(c) ≡ c then Th⋆ ⊑ c.

  Th⋆≤Flow-fixed
    : (c : CP.Con)
    → Endo.fn (Flow-Endo K) c ≡ c
    → CP._⊑_ Th⋆ c
  Th⋆≤Flow-fixed c eq =
    μ-induction∂ c (subst (λ x → CP._⊑_ x c) (sym eq) (CP.refl {c = c}))

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

  -- With antisymmetry (available in `InfiniteKernel.po`) you get equality at Th⋆.

  sandwich-fixed-at-Th⋆
    : (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → Endo.fn f Th⋆ ≡ Th⋆
  sandwich-fixed-at-Th⋆ f infl f≤tf =
    let open BulkBoundaryPO po using (po-bnd)
        open PartialOrder po-bnd using (antisym)
        p = sandwich-bounds-at-Th⋆ f infl f≤tf
    in antisym (snd p) (fst p)

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

  -- Sup monotonicity (derived from `least`): if f ≤ g pointwise then sup f ≤ sup g.

  supω-mono
    : ∀ (f g : ℕ → CP.Con)
    → (∀ n → CP._⊑_ (f n) (g n))
    → CP._⊑_ (OmegaCPO.supω ωCPO f) (OmegaCPO.supω ωCPO g)
  supω-mono f g fg =
    OmegaCPO.least ωCPO f (OmegaCPO.supω ωCPO g)
      (λ n → CP.trans (fg n) (OmegaCPO.ub ωCPO g n))

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
            step₂ = GuardedClosure.mono GTruth (f≤flow c)
            step₃ = GuardedClosure.idemp-lax GTruth c
        in CP.trans step₁ (CP.trans step₂ step₃))

  -- Stability-reflection schema (assumption record):
  -- if a predicate is (1) upward closed and (2) closed under ω-sups,
  -- then it holds at `Th⋆` whenever it holds on all approximants.

  record StablePredicate (P : CP.Con → Set ℓ) : Set (lsuc ℓ) where
    field
      upClosed : ∀ {x y} → CP._⊑_ x y → P x → P y
      supClosed : (f : ℕ → CP.Con)
                → (∀ n → CP._⊑_ (f n) (f (suc n)))
                → (∀ n → P (f n))
                → P (OmegaCPO.supω ωCPO f)

  stable-on-approximants→stable-on-Th⋆
    : ∀ {P : CP.Con → Set ℓ}
    → StablePredicate P
    → (∀ n → P (approxS n))
    → P Th⋆
  stable-on-approximants→stable-on-Th⋆ {P = P} SP Pn =
    let open StablePredicate SP
        chain  : ∀ n → CP._⊑_ (approxS n) (approxS (suc n))
        chain  = approx-mono-step
        Psup   = supClosed approxS chain Pn
        sup≤th = snd Th⋆-as-supω
    in upClosed sup≤th Psup
