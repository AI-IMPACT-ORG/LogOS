{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.InfoTheory.Shannon.DPI where

open import LogOS.Prelude hiding (_+_; _*_)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Fin using (Fin)
open import LogOS.Prelude.Product using (_×_; _,_)

open import LogOS.Domain.InfoTheory.Shannon.Facts
import LogOS.Domain.InfoTheory.Shannon.Core as Core
import LogOS.Theorems.Meta.ApplicationKit as AppKit
import LogOS.Domain.Complexity.DataProcessingInequality as AbsDPI
open import LogOS.Minimal.Con using (ConPreorder)

-- Data Processing Inequality (finite case), in the “LogOS facts-pack” style.
--
-- This module packages DPI as a derived theorem provided the facts pack supplies:
-- - log-sum inequality (already in `ShannonFacts`), and
-- - enough algebraic/positivity structure to pull a common factor out of `klTerm`.
--
-- The cancellation law below is the minimal “awesome” axiom for DPI:
-- it states that scaling both KL arguments by the same positive factor scales
-- the KL term linearly.

record DPIFacts : Set₁ where
  field
    F : ShannonFacts

  open ShannonFacts F public

  field
    -- Common-factor scaling for the total KL term.
    --
    -- For reals: (a·c) ln((a·c)/(b·c)) = (a ln(a/b))·c.
    klTerm-scale
      : ∀ {a b c}
      → Pos a → Pos b → Pos c
      → klTerm (a * c) (b * c) ≡ (klTerm a b) * c

module For (DF : DPIFacts) where
  open DPIFacts DF

  -- Re-export the Shannon core structures under the same facts pack.
  module C = Core.For F
  open C using (Dist; DistPos; Kernel; KernelPos; pushDistPos)

  KLfun : ∀ {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  KLfun a b = sum (λ i → klTerm (a i) (b i))

  push : ∀ {m n : ℕ} → Kernel m n → (Fin m → ℝ) → Fin n → ℝ
  push {m} {n} K p j = sum (λ i → p i * Kernel.K K i j)

  -- KL data processing: pushing both inputs through a (strictly positive) kernel
  -- cannot increase KL divergence.
  --
  -- This is the textbook DPI, stated purely in terms of `klTerm` and `logSumIneq`.
  KL-DPI
    : ∀ {m n : ℕ}
      (K : KernelPos m n)
      (P Q : DistPos m)
    → KLfun (push (KernelPos.ker K) (DistPos.p P)) (push (KernelPos.ker K) (DistPos.p Q))
      ≤ KLfun (DistPos.p P) (DistPos.p Q)
  KL-DPI {m} {n} K P Q =
      ≤-trans
        (sum-mono pointwise)
      (subst (λ x → x ≤ KLfun (DistPos.p P) (DistPos.p Q)) (sym rhs≡) S≤KL)
    where
      aij : Fin n → Fin m → ℝ
      aij j i = DistPos.p P i * Kernel.K (KernelPos.ker K) i j

      bij : Fin n → Fin m → ℝ
      bij j i = DistPos.p Q i * Kernel.K (KernelPos.ker K) i j

      pointwise
        : ∀ j
        → klTerm (sum (aij j)) (sum (bij j))
          ≤ sum (λ i → klTerm (aij j i) (bij j i))
      pointwise j =
        logSumIneq
          (aij j)
          (bij j)
          (λ i → ≤0-* (DistPos.p≥0 P i) (KernelPos.K≥0 K i j))
          (λ i → Pos-* (DistPos.pPos Q i) (KernelPos.rowPos K i j))

      rhs : ℝ
      rhs =
        sum (λ j → sum (λ i → klTerm (aij j i) (bij j i)))

      rhs≡ : rhs ≡ sum (λ i → (klTerm (DistPos.p P i) (DistPos.p Q i)) * 1#)
      rhs≡ =
        trans
          (sym (sum-swap (λ i j → klTerm (aij j i) (bij j i))))
          (sum-cong (λ i →
            trans
              (sum-cong (λ j → klTerm-scale (DistPos.pPos P i) (DistPos.pPos Q i) (KernelPos.rowPos K i j)))
              (trans
                (sum-*ˡ (klTerm (DistPos.p P i) (DistPos.p Q i)) (Kernel.K (KernelPos.ker K) i))
                (cong (λ x → (klTerm (DistPos.p P i) (DistPos.p Q i)) * x)
                      (Kernel.rowSum≡1 (KernelPos.ker K) i)))))

      klEq : KLfun (DistPos.p P) (DistPos.p Q) ≡ sum (λ i → (klTerm (DistPos.p P i) (DistPos.p Q i)) * 1#)
      klEq = sym (sum-cong (λ i → *-idr (klTerm (DistPos.p P i) (DistPos.p Q i))))

      S : ℝ
      S = sum (λ i → (klTerm (DistPos.p P i) (DistPos.p Q i)) * 1#)

      S≤KL : S ≤ KLfun (DistPos.p P) (DistPos.p Q)
      S≤KL =
        subst (λ x → S ≤ x) (sym klEq) (≤-refl {x = S})

  -- Bridge: Shannon KL-DPI as an instance of the generic “DPI-on-a-preorder” interface.
  --
  -- This uses the endo case (n ↦ n) so channels are genuine endomaps on observables.
  module AsAbstractDPI where

    ℝPreorder : ConPreorder lzero
    ℝPreorder = record
      { Con  = ℝ
      ; _⊑_  = _≤_
      ; refl = ≤-refl
      ; trans = ≤-trans
      }

    module ForN (n : ℕ) where
      Obs : Set₁
      Obs = DistPos n × DistPos n

      channels : AbsDPI.ChannelFamily Obs
      channels =
        record
          { Ch  = KernelPos n n
          ; run = λ K (P , Q) → (pushDistPos K P , pushDistPos K Q)
          }

      dpiKL : AbsDPI.DPIOn Obs channels ℝPreorder
      dpiKL =
        record
          { info = λ (P , Q) → KLfun (DistPos.p P) (DistPos.p Q)
          ; dpi  = λ K (P , Q) → KL-DPI K P Q
          }

-- Standard “quartet” wrapper to match the style used in Opacity and Universality.
module QuartetDPI where
  record Assumptions : Set₁ where
    field
      facts : DPIFacts

  Claim : Assumptions → Set₁
  Claim A =
    let
      DF = Assumptions.facts A
      open DPIFacts DF
      module D = For DF
    in
    ∀ {m n : ℕ} (K : Core.For.KernelPos F m n) (P Q : Core.For.DistPos F m) →
      D.KLfun
        (D.push (Core.For.KernelPos.ker K) (Core.For.DistPos.p P))
        (D.push (Core.For.KernelPos.ker K) (Core.For.DistPos.p Q))
      ≤ D.KLfun (Core.For.DistPos.p P) (Core.For.DistPos.p Q)

  derive : (A : Assumptions) → Claim A
  derive A K P Q = For.KL-DPI (Assumptions.facts A) K P Q

  module Q = AppKit.MakeDerived Assumptions Claim derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
