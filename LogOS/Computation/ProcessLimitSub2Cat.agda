{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.ProcessLimitSub2Cat where

-- “Limit-stable” sub-2-category for processes:
-- objects carry explicit ωCPO/continuity data (so `run∞` is defined),
-- 1-cells are lax process morphisms equipped with ω-continuity of the state map,
-- so they preserve `run∞` (via μ-fusion).
--
-- This mirrors `LogOS.Kernel.Hom2Cat.FlowSub2Cat`, but for `run∞`.

open import LogOS.Prelude

import LogOS.Minimal.Truth as Truth
open import LogOS.Computation.SchemeCategory using (Process; ProcessHomLax; idProcessHomLax; _∘ProcessHomLax_)
import LogOS.Computation.ProcessLimit as PL

module For
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  where

  record Obj : Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) where
    field
      P : Process {ℓO} {ℓC} {ℓQ} Output
      D : PL.For.LimitData P

  open Obj public

  record Hom₁ (A B : Obj) : Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) where
    private
      P₁ = Obj.P A
      P₂ = Obj.P B
    field
      hom  : ProcessHomLax P₁ P₂
      cont : PL.TransportLax.cont-map (Obj.D A) (Obj.D B) hom

  open Hom₁ public

  idHom₁ : ∀ (A : Obj) → Hom₁ A A
  idHom₁ A =
    record
      { hom  = idProcessHomLax (Obj.P A)
      ; cont = λ _ _ → Process.refl (Obj.P A)
      }

  composeHom₁
    : ∀ {A B C : Obj}
    → Hom₁ A B → Hom₁ B C → Hom₁ A C
  composeHom₁ {A} {B} {C} f g =
    record
      { hom  = Hom₁.hom g ∘ProcessHomLax Hom₁.hom f
      ; cont = cont-comp
      }
    where
      open Obj A using () renaming (P to P₁; D to D₁)
      open Obj B using () renaming (P to P₂; D to D₂)
      open Obj C using () renaming (P to P₃; D to D₃)

      open Process P₁ renaming (_⊑_ to _⊑₁_)
      open Process P₂ renaming (_⊑_ to _⊑₂_)
      open Process P₃ renaming (_⊑_ to _⊑₃_; trans to trans₃)

      h₁ : ProcessHomLax P₁ P₂
      h₁ = Hom₁.hom f

      h₂ : ProcessHomLax P₂ P₃
      h₂ = Hom₁.hom g

      map₁ : Process.Con P₁ → Process.Con P₂
      map₁ = ProcessHomLax.map h₁

      map₂ : Process.Con P₂ → Process.Con P₃
      map₂ = ProcessHomLax.map h₂

      mono-chain-map₁
        : ∀ (chain : ℕ → Process.Con P₁)
          (mono-chain : ∀ n → _⊑₁_ (chain n) (chain (suc n)))
        → ∀ n → _⊑₂_ (map₁ (chain n)) (map₁ (chain (suc n)))
      mono-chain-map₁ chain mono-chain n =
        ProcessHomLax.mono h₁ (mono-chain n)

      cont-comp
        : PL.TransportLax.cont-map D₁ D₃ (h₂ ∘ProcessHomLax h₁)
      cont-comp chain mono-chain =
        let
          -- First use ω-continuity of `map₁`, then ω-continuity of `map₂`.
          ω₁ = PL.For.LimitData.ωCPO D₁
          ω₂ = PL.For.LimitData.ωCPO D₂
          ω₃ = PL.For.LimitData.ωCPO D₃

          supω₁ = Truth.GuardedCore.OmegaCPO.supω ω₁
          supω₂ = Truth.GuardedCore.OmegaCPO.supω ω₂
          supω₃ = Truth.GuardedCore.OmegaCPO.supω ω₃

          le₁ : _⊑₃_ (map₂ (map₁ (supω₁ chain)))
                     (map₂ (supω₂ (λ n → map₁ (chain n))))
          le₁ =
            ProcessHomLax.mono h₂
              (Hom₁.cont f chain mono-chain)

          le₂ : _⊑₃_ (map₂ (supω₂ (λ n → map₁ (chain n))))
                     (supω₃ (λ n → map₂ (map₁ (chain n))))
          le₂ =
            Hom₁.cont g (λ n → map₁ (chain n)) (mono-chain-map₁ chain mono-chain)
        in
        trans₃ le₁ le₂

  preserves-run∞
    : ∀ {A B : Obj}
    → (h : Hom₁ A B)
    → ∀ c
    → Process._⊑_ (Obj.P B)
        (ProcessHomLax.map (Hom₁.hom h) (PL.For.run∞ (Obj.P A) (Obj.D A) c))
        (PL.For.run∞ (Obj.P B) (Obj.D B) (ProcessHomLax.map (Hom₁.hom h) c))
  preserves-run∞ {A} {B} h =
    PL.TransportLax.run∞-map≤ (Obj.D A) (Obj.D B) (Hom₁.hom h) (Hom₁.cont h)
