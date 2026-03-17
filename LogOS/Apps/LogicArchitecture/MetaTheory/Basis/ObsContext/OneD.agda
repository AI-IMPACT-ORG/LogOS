{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext.OneD where

-- 1D contexts (views on a single carrier)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _×CP_)
open import LogOS.LT.ConPreorder.Indexed using (IndexedConPreorder; mkIndexedConPreorder)
open import LogOS.LT.FunPreorder using (FunPreorder; DFunPreorder)
open import LogOS.LT.Presentation.ObservationInitiality using
  ( ProbeSuite
  ; DependentProbeSuite
  ; suiteView
  ; suiteViewᵈ
  )
open import LogOS.LT.View using
  ( View
  ; _⊑[_]_
  ; pairView
  ; pairView-fst
  ; pairView-snd
  ; pairView-intro
  )

record ObsContext {ℓX : Level} (X : Set ℓX) (ℓOCon ℓORel : Level)
  : Set (lsuc (ℓX ⊔ ℓOCon ⊔ ℓORel)) where
  field
    O : ConPreorder ℓOCon ℓORel
    V : View X O

-- Bridge: probe suites are bundled observation contexts.
--
-- These constructors reuse the canonical suite views from
-- `LogOS.LT.Presentation.ObservationInitiality`.

fromProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → ProbeSuite X I O
  → ObsContext X (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel)
fromProbeSuite {I = I} {O = O} S =
  record
    { O = FunPreorder I O
    ; V = suiteView S
    }

fromDependentProbeSuite
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → DependentProbeSuite X I O
  → ObsContext X (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel)
fromDependentProbeSuite {I = I} {O = O} S =
  record
    { O = DFunPreorder I O
    ; V = suiteViewᵈ S
    }

infix 4 _≤Ctx_
_≤Ctx_
  : ∀ {ℓX ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {X : Set ℓX}
  → ObsContext X ℓOCon₁ ℓORel₁
  → ObsContext X ℓOCon₂ ℓORel₂
  → Set (ℓX ⊔ ℓORel₁ ⊔ ℓORel₂)
C ≤Ctx C' =
  ∀ {x y}
  → x ⊑[ ObsContext.V C' ] y
  → x ⊑[ ObsContext.V C ] y

infixl 7 _⊔Ctx_
_⊔Ctx_
  : ∀ {ℓX ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {X : Set ℓX}
  → ObsContext X ℓOCon₁ ℓORel₁
  → ObsContext X ℓOCon₂ ℓORel₂
  → ObsContext X (ℓOCon₁ ⊔ ℓOCon₂) (ℓORel₁ ⊔ ℓORel₂)
C ⊔Ctx D =
  record
    { O = ObsContext.O C ×CP ObsContext.O D
    ; V = pairView (ObsContext.V C) (ObsContext.V D)
    }

≤Ctx-⊔₁
  : ∀ {ℓX ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {X : Set ℓX}
    (C : ObsContext X ℓOCon₁ ℓORel₁)
    (D : ObsContext X ℓOCon₂ ℓORel₂)
  → C ≤Ctx (C ⊔Ctx D)
≤Ctx-⊔₁ C D le =
  pairView-fst {V₁ = ObsContext.V C} {V₂ = ObsContext.V D} le

≤Ctx-⊔₂
  : ∀ {ℓX ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {X : Set ℓX}
    (C : ObsContext X ℓOCon₁ ℓORel₁)
    (D : ObsContext X ℓOCon₂ ℓORel₂)
  → D ≤Ctx (C ⊔Ctx D)
≤Ctx-⊔₂ C D le =
  pairView-snd {V₁ = ObsContext.V C} {V₂ = ObsContext.V D} le

⊔Ctx-least
  : ∀ {ℓX ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂ ℓOCon₃ ℓORel₃}
    {X : Set ℓX}
    {C : ObsContext X ℓOCon₁ ℓORel₁}
    {D : ObsContext X ℓOCon₂ ℓORel₂}
    {E : ObsContext X ℓOCon₃ ℓORel₃}
  → C ≤Ctx E
  → D ≤Ctx E
  → (C ⊔Ctx D) ≤Ctx E
⊔Ctx-least {C = C} {D = D} C≤E D≤E le =
  pairView-intro
    {V₁ = ObsContext.V C}
    {V₂ = ObsContext.V D}
    (C≤E le)
    (D≤E le)

-- Bridge: a context-indexed family of views yields an indexed refinement preorder.
ObsICP
  : ∀ {ℓI ℓX ℓOCon ℓORel}
    {Context : Set ℓI}
    {X : Set ℓX}
  → (ctx : Context → ObsContext X ℓOCon ℓORel)
  → IndexedConPreorder Context X ℓORel
ObsICP {Context = Context} {X = X} ctx =
  mkIndexedConPreorder
    (λ c x y → x ⊑[ ObsContext.V (ctx c) ] y)
    (λ {c} {x} →
      ConPreorder.refl (ObsContext.O (ctx c))
        {c = View.μ (ObsContext.V (ctx c)) x})
    (λ {c} {x} {y} {z} xy yz →
      let
        O = ObsContext.O (ctx c)
        module R = LogOS.Prelude.RefinementKit.Reasoning O
      in
      R._⊑⟨_⟩_ (View.μ (ObsContext.V (ctx c)) x) xy yz)
