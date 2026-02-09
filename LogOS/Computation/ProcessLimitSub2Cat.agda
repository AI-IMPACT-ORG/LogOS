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
-- We keep the original API (`Obj`, `Hom₁`, `idHom₁`, `composeHom₁`,
-- `preserves-run∞`) and also instantiate the generic
-- `LogOS.Kernel.Hom2Cat.FlowSub2Cat.With` checker over this continuity-marked
-- hom space.

open import LogOS.Prelude

import LogOS.Minimal.Truth as Truth
open import LogOS.Computation.SchemeCategory using (Process; ProcessHomLax; idProcessHomLax; _∘ProcessHomLax_)
import LogOS.Computation.ProcessLimit as PL
import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub

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

  -- Generic sub-2-category checker instantiated over the continuity-marked homs.
  -- Here continuity is already internal to `Hom₁`, so the external witness is
  -- the trivial marker `⊤`.
  private
    FlowWitness : ∀ {A B : Obj} → Hom₁ A B → Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
    FlowWitness _ = ⊤ {ℓ = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)}

    idFlowWitness : ∀ A → FlowWitness (idHom₁ A)
    idFlowWitness _ = tt {ℓ = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)}

    composeFlowWitness
      : ∀ {A B C : Obj}
        {f : Hom₁ A B}
        {g : Hom₁ B C}
      → FlowWitness f
      → FlowWitness g
      → FlowWitness (composeHom₁ f g)
    composeFlowWitness {A} {B} {C} {f} {g} _ _ =
      tt {ℓ = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)}

    module Sub = FlowSub.With
      {ℓObj = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)}
      {ℓHom = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)}
      {ℓFlow = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)}
      Obj
      Hom₁
      FlowWitness
      idHom₁
      composeHom₁
      idFlowWitness
      (λ {A} {B} {C} {f} {g} _ _ →
        tt {ℓ = lsuc (ℓO ⊔ ℓC ⊔ ℓQ)})

    sub-id-exists : ∀ A → Sub.Hom₁ᶠ A A
    sub-id-exists = Sub.idHom₁ᶠ

  preserves-run∞
    : ∀ {A B : Obj}
    → (h : Hom₁ A B)
    → ∀ c
    → Process._⊑_ (Obj.P B)
        (ProcessHomLax.map (Hom₁.hom h) (PL.For.run∞ (Obj.P A) (Obj.D A) c))
        (PL.For.run∞ (Obj.P B) (Obj.D B) (ProcessHomLax.map (Hom₁.hom h) c))
  preserves-run∞ {A} {B} h =
    PL.TransportLax.run∞-map≤ (Obj.D A) (Obj.D B) (Hom₁.hom h) (Hom₁.cont h)
