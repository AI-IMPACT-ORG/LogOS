{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Implementation2Cat.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Implementation-tier witnesses as a displayed layer over the architectural
-- boundary base `LOGᴳ`.
--
-- Reading:
-- - architecture: boundary morphisms and boundary-only refinement
-- - implementation: code-level witnesses realising architectural transport
-- - law: additional displayed doctrine layers may be stacked afterwards

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_; ≈-refl)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  ; DecoratedObj
  ; DecoratedHom
  ; mkTotalObjR
  ; mkTotalHomR
  ; forgetDecorated
  ; base
  ; baseHom
  ; dispHom
  )
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.Coherence using (CohMode; approx; under; CohLevel)

open import LogOS.LT.LOG.Boundary2Cat using
  ( LOGᴳ
  ; restrict⇒ᴳ
  )
import LogOS.LT.LOG.Kernel2Cat.Core as Kernel2Cat
import LogOS.LT.LOG.GuardedKernel2Cat as GuardedKernel2Cat

import LogOS.LT.Hom.Core as Hom
import LogOS.LT.BoundaryImplementation.Core as BoundaryImpl

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.Template.Singleton2Cat as Template

ImplementationDisplayedLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat
      (LOGᴳ {ℓ} {ℓRel} {ℓCode})
      lzero
      (ℓCode ⊔ CohLevel m ℓ ℓRel)
ImplementationDisplayedLike {m} {ℓ} {ℓRel} {ℓCode} =
  let
    C = LOGᴳ {ℓ} {ℓRel} {ℓCode}
    module C = Thin2Cat C
  in
  record
    { Ob = λ _ → ⊤ {ℓ = lzero}
    ; HomD =
        λ {K} {K'} (h∂ : Con (C.Hom K K')) _ _ →
          BoundaryImpl.BoundaryImplementation m (lower h∂)
    ; idD = λ {K} _ →
        BoundaryImpl.idBoundaryImplementation {m = m} K
    ; compD = λ {A} {B} {C₀} {f} {g} cf cg →
        BoundaryImpl.composeBoundaryImplementation
          {m = m}
          {K₁ = A}
          {K₂ = B}
          {K₃ = C₀}
          {f∂ = lower f}
          {g∂ = lower g}
          cg
          cf
    }

LOGᴳʳLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ CohLevel m ℓ ℓRel)
      (ℓ ⊔ ℓRel)
LOGᴳʳLike {m} {ℓ} {ℓRel} {ℓCode} =
  DecoratedThin2Cat (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})

ImplementationDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOGᴳ {ℓ} {ℓRel} {ℓCode}) lzero (ℓCode ⊔ ℓRel)
ImplementationDisplayed = ImplementationDisplayedLike {m = approx}

ImplementationDisplayedUnder
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOGᴳ {ℓ} {ℓRel} {ℓCode}) lzero (ℓCode ⊔ ℓRel)
ImplementationDisplayedUnder = ImplementationDisplayedLike {m = under}

LOGᴳʳ
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓRel)
      (ℓ ⊔ ℓRel)
LOGᴳʳ {ℓ} {ℓRel} {ℓCode} = LOGᴳʳLike {m = approx} {ℓ} {ℓRel} {ℓCode}

LOGᴳʳ⊑
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓRel)
      (ℓ ⊔ ℓRel)
LOGᴳʳ⊑ {ℓ} {ℓRel} {ℓCode} = LOGᴳʳLike {m = under} {ℓ} {ℓRel} {ℓCode}

LOGArchitectureImplementation = LOGᴳʳ
LOGArchitectureImplementationUnder = LOGᴳʳ⊑

embedLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode
  → DecoratedObj (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})
embedLike K = mkTotalObjR K (tt {ℓ = lzero})

embed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode
  → DecoratedObj (ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})
embed {ℓ} {ℓRel} {ℓCode} = embedLike {m = approx} {ℓ} {ℓRel} {ℓCode}

toKernelHomLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → DecoratedHom
      (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})
      (embedLike {m = m} K)
      (embedLike {m = m} K')
  → Hom.KernelHomLike m K K'
toKernelHomLike h =
  Hom.mkKernelHomParts (lower (baseHom h)) (dispHom h)

toKernelHom
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → DecoratedHom (ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}) (embed K) (embed K')
  → Hom.KernelHom K K'
toKernelHom {ℓ} {ℓRel} {ℓCode} = toKernelHomLike {m = approx} {ℓ} {ℓRel} {ℓCode}

toFacadeHom = toKernelHom

toKernelHomLike′
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {X Y : DecoratedObj (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})}
  → DecoratedHom (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}) X Y
  → Hom.KernelHomLike m
      (base {D = ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} X)
      (base {D = ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} Y)
toKernelHomLike′ h =
  Hom.mkKernelHomParts (lower (baseHom h)) (dispHom h)

toKernelHom′
  : ∀ {ℓ ℓRel ℓCode : Level}
    {X Y : DecoratedObj (ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})}
  → DecoratedHom (ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}) X Y
  → Hom.KernelHom
      (base {D = ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}} X)
      (base {D = ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}} Y)
toKernelHom′ h =
  Hom.mkKernelHomParts (lower (baseHom h)) (dispHom h)

fromKernelHomLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → Hom.KernelHomLike m K K'
  → DecoratedHom
      (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})
      (embedLike {m = m} K)
      (embedLike {m = m} K')
fromKernelHomLike {ℓCode = ℓCode} h =
  mkTotalHomR
    (lift {ℓ = ℓCode} (Hom.boundaryPart (Hom.toKernelHomLikeR h)))
    (Hom.implementationPart (Hom.toKernelHomLikeR h))

fromKernelHom
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → Hom.KernelHom K K'
  → DecoratedHom (ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}) (embed K) (embed K')
fromKernelHom {ℓ} {ℓRel} {ℓCode} = fromKernelHomLike {m = approx} {ℓ} {ℓRel} {ℓCode}

fromFacadeHom = fromKernelHom

forgetImplementationLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
  → Thin2Functor (LOGᴳʳLike {m = m} {ℓ} {ℓRel} {ℓCode}) (LOGᴳ {ℓ} {ℓRel} {ℓCode})
forgetImplementationLike {m} {ℓ} {ℓRel} {ℓCode} =
  forgetDecorated (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})

forgetImplementation
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor (LOGᴳʳ {ℓ} {ℓRel} {ℓCode}) (LOGᴳ {ℓ} {ℓRel} {ℓCode})
forgetImplementation {ℓ} {ℓRel} {ℓCode} = forgetImplementationLike {m = approx} {ℓ} {ℓRel} {ℓCode}

toLOG
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor (LOGᴳʳ {ℓ} {ℓRel} {ℓCode}) (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode})
toLOG {ℓ} {ℓRel} {ℓCode} =
  let
    D = ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}
    module S = Thin2Cat (LOGᴳʳ {ℓ} {ℓRel} {ℓCode})
    module T = Thin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode})
  in
  record
    { mapObj = base {D = D}
    ; mapHom = λ {A} {B} h → toKernelHom′ {ℓ} {ℓRel} {ℓCode} {X = A} {Y = B} h
    ; mapHom-mono = λ {A} {B} {f} {g} le γ →
        restrict⇒ᴳ
          {K = base {D = D} A}
          {K' = base {D = D} B}
          {f = baseHom {D = D} {X = A} {Y = B} f}
          {g = baseHom {D = D} {X = A} {Y = B} g}
          le
          γ
    ; id-pres = λ {A} →
        ≈-refl
          (T.Hom (base {D = D} A) (base {D = D} A))
          (toKernelHom′ {ℓ} {ℓRel} {ℓCode} {X = A} {Y = A} (S.id {A}))
    ; comp-pres = λ {A} {B} {C₀} f g →
        ≈-refl
          (T.Hom (base {D = D} A) (base {D = D} C₀))
          (toKernelHom′
            {ℓ} {ℓRel} {ℓCode}
            {X = A} {Y = C₀}
            (S._∘_ {A = A} {B = B} {C = C₀} f g))
    }

toLOGUnder
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor (LOGᴳʳ⊑ {ℓ} {ℓRel} {ℓCode}) (GuardedKernel2Cat.LOG⊑ {ℓ} {ℓRel} {ℓCode})
toLOGUnder {ℓ} {ℓRel} {ℓCode} =
  let
    D = ImplementationDisplayedUnder {ℓ} {ℓRel} {ℓCode}
    module S = Thin2Cat (LOGᴳʳ⊑ {ℓ} {ℓRel} {ℓCode})
    module T = Thin2Cat (GuardedKernel2Cat.LOG⊑ {ℓ} {ℓRel} {ℓCode})
  in
  record
    { mapObj = base {D = D}
    ; mapHom = λ {A} {B} h → toKernelHomLike′ {m = under} {ℓ} {ℓRel} {ℓCode} {X = A} {Y = B} h
    ; mapHom-mono = λ {A} {B} {f} {g} le c →
        le c
    ; id-pres = λ {A} →
        ≈-refl
          (T.Hom (base {D = D} A) (base {D = D} A))
          (toKernelHomLike′ {m = under} {ℓ} {ℓRel} {ℓCode} {X = A} {Y = A} (S.id {A}))
    ; comp-pres = λ {A} {B} {C₀} f g →
        ≈-refl
          (T.Hom (base {D = D} A) (base {D = D} C₀))
          (toKernelHomLike′
            {m = under} {ℓ} {ℓRel} {ℓCode}
            {X = A} {Y = C₀}
            (S._∘_ {A = A} {B = B} {C = C₀} f g))
    }

toFacadeLOG = toLOG

data ImplementationTag : Set where
  implementation : ImplementationTag

implementationTagId : ℕ
implementationTagId = 22

private
  module ImplementationPort {m : CohMode} {ℓ ℓRel ℓCode : Level} =
    Template.SingletonLayer
      implementationTagId
      {Tag = ImplementationTag}
      (ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})

implementationSigLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOGᴳ {ℓ} {ℓRel} {ℓCode}) implementationTagId ImplementationTag
implementationSigLike {m} {ℓ} {ℓRel} {ℓCode} =
  ImplementationPort.portSig {m = m} {ℓ} {ℓRel} {ℓCode}

implementationSingletonLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
  → PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ImplementationTag
implementationSingletonLike {m} {ℓ} {ℓRel} {ℓCode} =
  ImplementationPort.singleton {m = m} {ℓ} {ℓRel} {ℓCode}

implementationSig
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOGᴳ {ℓ} {ℓRel} {ℓCode}) implementationTagId ImplementationTag
implementationSig = implementationSigLike {m = approx}

implementationSingleton
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ImplementationTag
implementationSingleton {ℓ} {ℓRel} {ℓCode} = implementationSingletonLike {m = approx} {ℓ} {ℓRel} {ℓCode}

-- Generic architecture helper: given any law stack over `LOGᴳ`, prepend the
-- implementation layer to obtain the corresponding implementation-enriched
-- stack over the same boundary basis.
implementationStackLike
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (implementationSingleton : PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ImplementationTag)
  → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
implementationStackLike implementationSingleton S =
  PortStack.SingletonPort.entry implementationSingleton
    PortStack.∷⁺
      S

implementationStack
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
implementationStack {ℓ} {ℓRel} {ℓCode} =
  implementationStackLike (implementationSingleton {ℓ} {ℓRel} {ℓCode})

implementationStackUnder
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
  → PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})
implementationStackUnder {ℓ} {ℓRel} {ℓCode} =
  implementationStackLike
    (implementationSingletonLike {m = under} {ℓ} {ℓRel} {ℓCode})

private
  stackIdSubstack
    : ∀ {ℓ ℓRel ℓCode : Level}
      {S : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})}
    → PortStack.Substack S S
  stackIdSubstack {S = PortStack.[ p ]} = PortStack.last
  stackIdSubstack {S = p PortStack.∷⁺ S} =
    PortStack.keep stackIdSubstack

  dropImplementationSubstack
    : ∀ {ℓ ℓRel ℓCode : Level}
      (implementationSingleton : PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ImplementationTag)
      {S : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})}
    → PortStack.Substack S (implementationStackLike implementationSingleton S)
  dropImplementationSubstack implementationSingleton {S = S} =
    PortStack.drop (stackIdSubstack {S = S})

forgetImplementationStackLike
  : ∀ {ℓ ℓRel ℓCode : Level}
    (implementationSingleton : PortStack.SingletonPort (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ImplementationTag)
    {S : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})}
  → Thin2Functor
      (PortStack.StackCat (implementationStackLike implementationSingleton S))
      (PortStack.StackCat S)
forgetImplementationStackLike implementationSingleton {S = S} =
  PortStack.forgetSubstack (dropImplementationSubstack implementationSingleton {S = S})

forgetImplementationStack
  : ∀ {ℓ ℓRel ℓCode : Level}
    {S : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})}
  → Thin2Functor
      (PortStack.StackCat (implementationStack S))
      (PortStack.StackCat S)
forgetImplementationStack {ℓ} {ℓRel} {ℓCode} {S = S} =
  forgetImplementationStackLike
    (implementationSingleton {ℓ} {ℓRel} {ℓCode})
    {S = S}

forgetImplementationStackUnder
  : ∀ {ℓ ℓRel ℓCode : Level}
    {S : PortStack.PortStack (LOGᴳ {ℓ} {ℓRel} {ℓCode})}
  → Thin2Functor
      (PortStack.StackCat (implementationStackUnder {ℓ} {ℓRel} {ℓCode} S))
      (PortStack.StackCat S)
forgetImplementationStackUnder {ℓ} {ℓRel} {ℓCode} {S = S} =
  forgetImplementationStackLike
    (implementationSingletonLike {m = under} {ℓ} {ℓRel} {ℓCode})
    {S = S}
