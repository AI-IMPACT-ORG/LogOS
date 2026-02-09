{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Infinite where

-- Kernel-independent ω/μ infrastructure:
-- generic facts about the distinguished guarded fixed point Th* once a boundary
-- preorder carries ωCPO structure and a FiniteFirst approximation story.

open import LogOS.Prelude

open import LogOS.Prelude using (_×_; _,_; fst; snd)
open import LogOS.Prelude.Ordinal as Ord

open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

module For
  {ℓ : Level}
  (CP : ConPreorder ℓ)
  (GC : Truth.GuardedCore.GuardedClosure CP)
  (ωCPO : Truth.GuardedCore.OmegaCPO CP)
  (FF : Truth.GuardedCore.FiniteFirst CP GC ωCPO)
  where

  open ConPreorder CP renaming (refl to refl≤ ; trans to trans≤)
  open Truth.GuardedCore hiding (μ-induction)
  open GuardedClosure GC renaming (Flow to F; Th* to Th⋆)
  open OmegaCPO ωCPO
  open FiniteFirst FF public
    renaming
      ( approxS     to approxS
      ; base        to baseEq
      ; step        to stepEq
      ; Th⋆-as-sup  to supEq
      )

  module K = Truth.GuardedCore.Kleene {CP = CP} ωCPO

  Th⋆-as-supω
    : _⊑_ Th⋆ (supω approxS)
      × _⊑_ (supω approxS) Th⋆
  Th⋆-as-supω = supEq

  -- Approximants are an increasing ω-chain.

  approx-mono-step
    : ∀ n → _⊑_ (approxS n) (approxS (suc n))
  approx-mono-step n =
    subst (λ x → _⊑_ (approxS n) x) (sym (stepEq n)) (infl (approxS n))

  approx-mono
    : ∀ {m n} → Ord._≤ℕ_ m n → _⊑_ (approxS m) (approxS n)
  approx-mono {m} {n} Ord.z≤n =
    subst (λ x → _⊑_ x (approxS n)) (sym baseEq) (isBot (approxS n))
  approx-mono {m = suc m} {n = suc n} (Ord.s≤s mn) =
    let
      leF : _⊑_ (F (approxS m)) (F (approxS n))
      leF = mono (approx-mono {m = m} {n = n} mn)
      leR : _⊑_ (F (approxS m)) (approxS (suc n))
      leR = subst (λ y → _⊑_ (F (approxS m)) y) (sym (stepEq n)) leF
    in
    subst (λ x → _⊑_ x (approxS (suc n))) (sym (stepEq m)) leR

  -- Approximation principle: to bound Th⋆, it suffices to bound all approximants.

  approx-all→supω≤
    : (c : Con)
    → (∀ n → _⊑_ (approxS n) c)
    → _⊑_ (supω approxS) c
  approx-all→supω≤ c ub = least approxS c ub

  approx-all→Th⋆≤
    : (c : Con)
    → (∀ n → _⊑_ (approxS n) c)
    → _⊑_ Th⋆ c
  approx-all→Th⋆≤ c ub =
    let
      th≤sup = ≈CP⇒ {CP = CP} Th⋆-as-supω
      sup≤c  = approx-all→supω≤ c ub
    in trans≤ th≤sup sup≤c

  -- μ-induction: any Flow-pre-fixed point upper-bounds Th⋆.

  μ-induction
    : (c : Con)
    → _⊑_ (F c) c
    → _⊑_ Th⋆ c
  μ-induction c pre =
    Truth.GuardedCore.μ-induction {CP = CP} GC ωCPO FF c pre

  -- Corollary: if Flow(c) ≡ c then Th⋆ ⊑ c.

  Th⋆≤Flow-fixed
    : (c : Con)
    → F c ≡ c
    → _⊑_ Th⋆ c
  Th⋆≤Flow-fixed c eq =
    μ-induction c (subst (λ x → _⊑_ x c) (sym eq) (refl≤ {c = c}))

  -- Sup monotonicity (derived from `least`): if f ≤ g pointwise then sup f ≤ sup g.

  supω-mono
    : ∀ (f g : ℕ → Con)
    → (∀ n → _⊑_ (f n) (g n))
    → _⊑_ (supω f) (supω g)
  supω-mono f g fg = K.supω-mono {f = f} {g = g} fg

  -- With antisymmetry you get equality at Th⋆.

  FlowTh⋆≡Th⋆
    : PartialOrder CP
    → F Th⋆ ≡ Th⋆
  FlowTh⋆≡Th⋆ po =
    PartialOrder.antisym po (≈CP⇐ {CP = CP} Th*-fixed) (≈CP⇒ {CP = CP} Th*-fixed)

  -- Stability-reflection schema (assumption record):
  -- if a predicate is (1) upward closed and (2) closed under ω-sups,
  -- then it holds at `Th⋆` whenever it holds on all approximants.

  record StablePredicate (P : Con → Set ℓ) : Set (lsuc ℓ) where
    field
      upClosed : ∀ {x y} → _⊑_ x y → P x → P y
      supClosed
        : (f : ℕ → Con)
        → (∀ n → _⊑_ (f n) (f (suc n)))
        → (∀ n → P (f n))
        → P (supω f)

  stable-on-approximants→stable-on-Th⋆
    : ∀ {P : Con → Set ℓ}
    → StablePredicate P
    → (∀ n → P (approxS n))
    → P Th⋆
  stable-on-approximants→stable-on-Th⋆ {P = P} SP Pn =
    let
      open StablePredicate SP
      Psup   = supClosed approxS approx-mono-step Pn
      sup≤th = ≈CP⇐ {CP = CP} Th⋆-as-supω
    in upClosed sup≤th Psup
