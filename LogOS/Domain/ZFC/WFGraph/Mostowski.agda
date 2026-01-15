{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.Mostowski where

-- Mostowski-style collapse for WF-graphs: fold ∘ unfold.
-- This is a lightweight, extensionality-free version: it shows how membership
-- is transported along the collapse map.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import LogOS.Domain.ZFC.SetU.WFGraphCore as Core
open import LogOS.Domain.ZFC.SetU.GraphTreeBridge as Bridge

module For
  {ℓ : Level}
  (G : Core.WFGraph ℓ)
  (S : Bridge.SupStructure G)
  where
  open Core.WFGraph G renaming (Node to N; Edge to E)

  mem-sup↔B = Bridge.SupStructure.mem-sup↔ S

  foldB : Core.Tree N → N
  foldB = Bridge.fold S

  collapseAcc : ∀ {x} → Core.Acc (λ y x → E x y) x → N
  collapseAcc a = foldB (Core.unfoldAcc G a)

  collapse : N → N
  collapse x = collapseAcc (Core.wf G x)

  -- Use the same accessibility witness for parent/child to avoid proof-irrelevance.
  collapseChildAcc : ∀ {x} (a : Core.Acc (λ y x → E x y) x) {y} → E x y → N
  collapseChildAcc (Core.acc step) {y} e = collapseAcc (step y e)

  collapseChild : ∀ {x y} → E x y → N
  collapseChild {x} e = collapseChildAcc (Core.wf G x) e

  -- Forward direction: membership in the graph transports to membership
  -- after collapse.
  collapse-edge→-acc
    : ∀ {x} (a : Core.Acc (λ y x → E x y) x) {y}
    → (e : E x y)
    → E (collapseAcc a) (collapseChildAcc a e)
  collapse-edge→-acc {x} (Core.acc step) {y} e =
    _↔_.from
      (mem-sup↔B
        {I = Σ N (λ y → E x y)}
        {f = λ { (y' , e') → foldB (Core.unfoldAcc G (step y' e')) }}
        {y = collapseAcc (step y e)})
      ((y , e) , refl)

  collapse-edge→
    : ∀ {x y}
    → (e : E x y)
    → E (collapse x) (collapseChild e)
  collapse-edge→ {x} e = collapse-edge→-acc (Core.wf G x) e

  -- Backward direction (up to collapse image): any edge out of `collapse x`
  -- comes from some edge out of `x`, with the target in the collapse image.
  collapse-edge←-acc
    : ∀ {x} (a : Core.Acc (λ y x → E x y) x) {z}
    → E (collapseAcc a) z
    → Σ N (λ y → Σ (E x y) (λ e → collapseChildAcc a e ≡ z))
  collapse-edge←-acc {x} (Core.acc step) {z} ez =
    let
      w = _↔_.to
            (mem-sup↔B
              {I = Σ N (λ y → E x y)}
              {f = λ { (y' , e') → foldB (Core.unfoldAcc G (step y' e')) }}
              {y = z})
            ez
    in
    let i = proj₁ w
        eq = proj₂ w
    in (proj₁ i , proj₂ i , eq)

  collapse-edge←
    : ∀ {x z}
    → E (collapse x) z
    → Σ N (λ y → Σ (E x y) (λ e → collapseChild e ≡ z))
  collapse-edge← {x} ez = collapse-edge←-acc (Core.wf G x) ez
