{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Reachability.Graded where

open import LogOS.Prelude

open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Truth as Truth

-- Q-graded reachability induced by a graded guarded closure:
-- `c ⟶[ g ] d` means “with grade/budget g, d is reachable from c”.
--
-- The only structure used is what `GradedClosure` already provides:
-- grade monotonicity + lax composition.

module For
  {ℓ : Level}
  {Q : QAdapter ℓ}
  {CP : ConPoset ℓ}
  (G : Truth.GuardedCore.GradedClosure Q CP)
  where

  open QAdapter Q renaming
    ( Scale to Grade
    ; _≤s_ to _≤g_
    ; _⊔s_ to _⊔g_
    ; _·_  to _∙_
    )
  open ConPoset CP
  open Truth.GuardedCore.GradedClosure G

  trans⊑ : ∀ {x y z} → _⊑_ x y → _⊑_ y z → _⊑_ x z
  trans⊑ = ConPoset.trans CP

  infix 4 _⟶[_]_

  _⟶[_]_ : Con → Grade → Con → Set ℓ
  c ⟶[ g ] d = _⊑_ d (Flow g c)

  ⟶-mono-grade
    : ∀ {c d g g'}
    → _≤g_ g g'
    → c ⟶[ g ] d
    → c ⟶[ g' ] d
  ⟶-mono-grade le reach =
    trans⊑ reach (mono-grade le _)

  ⟶-mono-src
    : ∀ {c c' d g}
    → _⊑_ c c'
    → c ⟶[ g ] d
    → c' ⟶[ g ] d
  ⟶-mono-src le reach =
    trans⊑ reach (mono le)

  ⟶-mono-tgt
    : ∀ {c d d' g}
    → _⊑_ d' d
    → c ⟶[ g ] d
    → c ⟶[ g ] d'
  ⟶-mono-tgt le reach =
    trans⊑ le reach

  ⟶-comp
    : ∀ {c d e g g'}
    → c ⟶[ g ] d
    → d ⟶[ g' ] e
    → c ⟶[ g ∙ g' ] e
  ⟶-comp {c = c} {d = d} {e = e} {g = g} {g' = g'} c→d d→e =
    let
      step₁ : _⊑_ (Flow g' d) (Flow g' (Flow g c))
      step₁ = mono c→d

      step₂ : _⊑_ (Flow g' (Flow g c)) (Flow (g ∙ g') c)
      step₂ = comp-lax g g' c
    in
    trans⊑ d→e (trans⊑ step₁ step₂)

  ⟶-⊔g₁
    : ∀ {c d g g'}
    → c ⟶[ g ] d
    → c ⟶[ g ⊔g g' ] d
  ⟶-⊔g₁ {g = g} {g' = g'} =
    ⟶-mono-grade (QAdapter.⊔s-ub₁ Q g g')

  ⟶-⊔g₂
    : ∀ {c d g g'}
    → c ⟶[ g' ] d
    → c ⟶[ g ⊔g g' ] d
  ⟶-⊔g₂ {g = g} {g' = g'} =
    ⟶-mono-grade (QAdapter.⊔s-ub₂ Q g g')

  ⟶-⊔g
    : ∀ {c d g g'}
    → (c ⟶[ g ] d) ⊎ (c ⟶[ g' ] d)
    → c ⟶[ g ⊔g g' ] d
  ⟶-⊔g (inj₁ p) = ⟶-⊔g₁ p
  ⟶-⊔g (inj₂ p) = ⟶-⊔g₂ p

  satReach : Con → Con → Set ℓ
  satReach c d = c ⟶[ sat ] d

  satReach-refl : ∀ c → satReach c c
  satReach-refl c = infl-sat c
