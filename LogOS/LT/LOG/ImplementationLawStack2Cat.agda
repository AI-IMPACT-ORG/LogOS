{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ImplementationLawStack2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Generic implementation-plus-law stack packaging over `LOGᴳ`.
--
-- This factors the common shape used by the contract and flow routes:
-- prepend the implementation witness layer, add one further displayed law port
-- over the same boundary base, then forget to the corresponding law-only
-- totalisation over kernel morphisms.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; Ob
  ; HomD
  ; DecoratedObj
  ; DecoratedThin2Cat
  ; mkTotalObjR
  ; mkTotalHomR
  ; base
  ; baseHom
  ; byBaseHom≡
  )
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Coherence using (approx; under)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)

open import LogOS.LT.LOG.Boundary2Cat using
  ( LOGᴳ
  ; restrict⇒ᴳ
  )
import LogOS.LT.LOG.Kernel2Cat.Core as Kernel2Cat
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat

import LogOS.LT.Hom.Core as Hom
import LogOS.LT.BoundaryImplementation.Core as BoundaryImpl

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.Template.Singleton2Cat as Template

module Build
  {ℓ ℓRel ℓCode ℓLawObjᴳ ℓLawHomᴳ ℓLawObj ℓLawHom : Level}
  (LawTag : Set)
  (LawDisplayedᴳ : DisplayedThin2Cat (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ℓLawObjᴳ ℓLawHomᴳ)
  (LawDisplayed : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓLawObj ℓLawHom)
  (mapLawObj : ∀ {K : Kernel ℓ ℓRel ℓCode} → Ob LawDisplayedᴳ K → Ob LawDisplayed K)
  (mapLawHom :
    ∀ {K K' : Kernel ℓ ℓRel ℓCode}
      (h∂ : Con (Thin2Cat.Hom (LOGᴳ {ℓ} {ℓRel} {ℓCode}) K K'))
      (implementation : BoundaryImpl.BoundaryImplementation approx (lower h∂))
      {x : Ob LawDisplayedᴳ K}
      {y : Ob LawDisplayedᴳ K'}
    → HomD LawDisplayedᴳ h∂ x y
    → HomD
        LawDisplayed
        (Hom.mkKernelHomParts (lower h∂) implementation)
        (mapLawObj x)
        (mapLawObj y))
  where

  private
    module LawPort =
      Template.SingletonLayer
        {Tag = LawTag}
        LawDisplayedᴳ

  lawSig
    : PortSig.PortSig (LOGᴳ {ℓ} {ℓRel} {ℓCode}) LawTag
  lawSig =
    LawPort.portSig

  lawSingleton
    : PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) LawTag
  lawSingleton =
    LawPort.singleton

  lawStackᴳ
    : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  lawStackᴳ =
    PortStack.SingletonPort.stack lawSingleton

  ImplementationLawStackLike
    : PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) Implementation2Cat.ImplementationTag
    → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  ImplementationLawStackLike implementationSingleton =
    Implementation2Cat.implementationStackLike implementationSingleton lawStackᴳ

  ImplementationLawStack
    : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  ImplementationLawStack =
    Implementation2Cat.implementationStack lawStackᴳ

  ImplementationLawStackUnder
    : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  ImplementationLawStackUnder =
    Implementation2Cat.implementationStackUnder lawStackᴳ

  ImplementationLawCatLike
    : (implementationSingleton : PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) Implementation2Cat.ImplementationTag)
    → Thin2Cat
        ( lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)
        ⊔ PortStack.StackℓDObj (ImplementationLawStackLike implementationSingleton)
        )
        ( (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
        ⊔ PortStack.StackℓDHom (ImplementationLawStackLike implementationSingleton)
        )
        (ℓ ⊔ ℓRel)
  ImplementationLawCatLike implementationSingleton =
    PortStack.StackCat (ImplementationLawStackLike implementationSingleton)

  ImplementationLawCat
    : Thin2Cat
        ( lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)
        ⊔ PortStack.StackℓDObj ImplementationLawStack
        )
        ( (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
        ⊔ PortStack.StackℓDHom ImplementationLawStack
        )
        (ℓ ⊔ ℓRel)
  ImplementationLawCat =
    ImplementationLawCatLike Implementation2Cat.implementationSingleton

  ImplementationLawCatUnder
    : Thin2Cat
        ( lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)
        ⊔ PortStack.StackℓDObj ImplementationLawStackUnder
        )
        ( (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
        ⊔ PortStack.StackℓDHom ImplementationLawStackUnder
        )
        (ℓ ⊔ ℓRel)
  ImplementationLawCatUnder =
    ImplementationLawCatLike
      (Implementation2Cat.implementationSingletonLike {m = under})

  ImplementationLawKernel
    : Set _
  ImplementationLawKernel =
    DecoratedObj (PortStack.StackDisplayed ImplementationLawStack)

  kernel
    : ImplementationLawKernel
    → Kernel ℓ ℓRel ℓCode
  kernel X =
    PortStack.baseObj {S = ImplementationLawStack} X

  private
    implementationPort
      : PortStack.HasPort
          (PortStack.SingletonPort.entry Implementation2Cat.implementationSingleton)
          ImplementationLawStack
    implementationPort =
      PortStack.hasHead {ps = lawStackᴳ}

    lawPort
      : PortStack.HasPort
          (PortStack.SingletonPort.entry lawSingleton)
          ImplementationLawStack
    lawPort =
      PortStack.hasThere {S = lawStackᴳ} PortStack.hasSingleton

  lawOf
    : (X : ImplementationLawKernel)
    → Ob LawDisplayed (kernel X)
  lawOf X =
    mapLawObj (PortStack.getObj lawPort X)

  forgetImplementationLaw
    : Thin2Functor ImplementationLawCat (DecoratedThin2Cat LawDisplayed)
  forgetImplementationLaw =
    record
      { mapObj = mapObj′
      ; mapHom = λ {A} {B} h → mapHom′ {A} {B} h
      ; mapHom-mono = λ {A} {B} {f} {g} le γ →
          restrict⇒ᴳ
            {K = base {D = D} A}
            {K' = base {D = D} B}
            {f = baseHom {D = D} {X = A} {Y = B} f}
            {g = baseHom {D = D} {X = A} {Y = B} g}
            le
            γ
      ; id-pres = λ {A} →
          byBaseHom≡ {D = LawDisplayed} {X = mapObj′ A} {Y = mapObj′ A}
            (mapHom′ {A = A} {B = A} (Src.id {A = A}))
            (Tgt.id {A = mapObj′ A})
            refl
      ; comp-pres = λ {A} {B} {C₀} f g →
          byBaseHom≡ {D = LawDisplayed} {X = mapObj′ A} {Y = mapObj′ C₀}
            (mapHom′ {A = A} {B = C₀} (Src._∘_ {A = A} {B = B} {C = C₀} f g))
            (mapHom′ {A = B} {B = C₀} f Tgt.∘ mapHom′ {A = A} {B = B} g)
            refl
      }
    where
      S = ImplementationLawStack
      D = PortStack.StackDisplayed S

      module Src = Thin2Cat (PortStack.StackCat S)
      module Tgt = Thin2Cat (DecoratedThin2Cat LawDisplayed)

      mapObj′ : DecoratedObj D → DecoratedObj LawDisplayed
      mapObj′ X =
        mkTotalObjR
          (base {D = D} X)
          (mapLawObj (PortStack.getObj lawPort X))

      mapHom′
        : ∀ {A B}
        → Con (Src.Hom A B)
        → Con (Tgt.Hom (mapObj′ A) (mapObj′ B))
      mapHom′ {A} {B} h =
        mkTotalHomR
          (Hom.mkKernelHomParts
            (lower (baseHom {D = D} {X = A} {Y = B} h))
            (PortStack.getHom implementationPort h))
          (mapLawHom
            (baseHom {D = D} {X = A} {Y = B} h)
            (PortStack.getHom implementationPort h)
            (PortStack.getHom lawPort h))
