{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.KernelToPar where

-- Bridge: interpret kernel morphisms extensionally as *total* partial maps on code.
--
-- Key design choice:
-- we use `CodePreorder` as the object mapping (not the boundary preorder),
-- because `LOG` compares morphisms by *boundary-driven* decoded behaviour on
-- code (`f ⇒∂ g` in `LogOS.LT.Hom`, i.e. pullback along `transportView`).
--
-- Via `decode-mapCode`, this order is equivalent to the “run the implementation then
-- decode” picture (`obsView`), and we use that bridge (`⇒∂→⇒`) when proving
-- monotonicity of the forgetful functor below.
--
-- Optional strengthening:
-- given an explicit CH2008 indexing ledger on `Par` (`ParTuringLedger`),
-- `codeToParTracked` lifts `codeToPar` into the Grothendieck/Σ-totalisation
-- `ParTracked U TU` of tracked partial maps.
-- (Refinement in the totalisation is inherited from the base; displayed evidence is proof-irrelevant.)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; refl⊑; MonoMap)
open import LogOS.LT.Kernel using (Kernel; Code; CodePreorder; bnd; decode)
open import LogOS.LT.Hom using (KernelHom; mapCode; map∂-mono; decode-mapCode; ⇒∂→⇒)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; _∘F_)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Presentation using
  ( Presentation
  ; CompletePresentation
  ; canonicalPresentation
  ; canonicalComplete
  ; presentation↔canonical
  )
open import LogOS.LT.Presentation.Independence using (presentationsAgree)
open import LogOS.Syntax.Prop using (_↔_; intro; to; from; ↔-sym; ↔-trans)
open import LogOS.LT.Theorems.Centering as Centering using (ContractibleFiber; NoSemanticFork)

import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.Lift using (LiftCP; some)
open import LogOS.Apps.TuringCategory.Lift using (transLiftCP)
import LogOS.Apps.TuringCategory.ParTracked as Tracked
import LogOS.Apps.TuringCategory.ParTuring as ParT
import LogOS.Ports.Opacity.Port as Opacity

record BoundaryObservationPort
  {ℓ ℓRel ℓCode ℓObs : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (O : ConPreorder ℓObs ℓRel)
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓObs)) where
  constructor mkBoundaryObservationPortFromPort
  field
    boundaryPort : Opacity.OpacityPort (Con (bnd K)) (LiftCP O)
    boundaryView-mono : MonoMap (bnd K) (LiftCP O) (μ (Opacity.toView boundaryPort))

  boundaryView : View (Con (bnd K)) (LiftCP O)
  boundaryView = Opacity.toView boundaryPort

  codeView : View (Code K) (LiftCP O)
  codeView = record { μ = λ γ → μ boundaryView (decode K γ) }

  canonicalCodePresentation : Presentation codeView
  canonicalCodePresentation = canonicalPresentation codeView

  canonicalCodeComplete : CompletePresentation canonicalCodePresentation
  canonicalCodeComplete = canonicalComplete codeView

open BoundaryObservationPort public

mkBoundaryObservationPort
  : ∀ {ℓ ℓRel ℓCode ℓObs : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {O : ConPreorder ℓObs ℓRel}
  → (V : View (Con (bnd K)) (LiftCP O))
  → MonoMap (bnd K) (LiftCP O) (μ V)
  → BoundaryObservationPort K O
mkBoundaryObservationPort V monoV =
  mkBoundaryObservationPortFromPort (Opacity.fromView V) monoV

codePartialMap
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {O : ConPreorder ℓCode ℓRel}
  → BoundaryObservationPort K O
  → PM.PartialMap (CodePreorder K) O
codePartialMap {K = K} Pₒ =
  record
    { map = λ γ → μ (boundaryView Pₒ) (decode K γ)
    ; mono = boundaryView-mono Pₒ
    }

kernelHomToPartialMap
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → KernelHom K K'
  → PM.PartialMap (CodePreorder K) (CodePreorder K')
kernelHomToPartialMap {K = K} {K' = K'} h =
  record
    { map = λ γ → some {CP = CodePreorder K'} (mapCode h γ)
    ; mono = mono
    }
  where
    mono
      : ∀ {γ δ}
      → _⊑_ (CodePreorder K) γ δ
      → _⊑_ (LiftCP (CodePreorder K'))
          (some {CP = CodePreorder K'} (mapCode h γ))
          (some {CP = CodePreorder K'} (mapCode h δ))
    mono {γ} {δ} γ⊑δ
      =
      let
        module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K')
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)

        lawγ = decode-mapCode h γ
        lawδ = decode-mapCode h δ
      in
      begin⊑
        decode K' (mapCode h γ)
          ⊑⟨ fst lawγ ⟩
        LogOS.LT.Hom.map∂ h (decode K γ)
          ⊑⟨ map∂-mono h γ⊑δ ⟩
        LogOS.LT.Hom.map∂ h (decode K δ)
          ⊑⟨ snd lawδ ⟩
        decode K' (mapCode h δ) ∎⊑

-- Observation gate on a kernel's *code*:
-- post-compose the canonical decode observation with a lifted `View`.
observeOnCode
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {O : ConPreorder ℓCode ℓRel}
  → (V : View (Con (bnd K)) (LiftCP O))
  → (monoV : MonoMap (bnd K) (LiftCP O) (μ V))
  → PM.PartialMap (CodePreorder K) O
observeOnCode {K = K} {O = O} V monoV =
  record
    { map = λ γ → μ V (decode K γ)
    ; mono = mono
    }
  where
    mono
      : ∀ {γ δ}
      → _⊑_ (CodePreorder K) γ δ
      → _⊑_ (LiftCP O)
          (μ V (decode K γ))
          (μ V (decode K δ))
    mono γ⊑δ = monoV γ⊑δ

boundaryObservationPresentationsAgree
  : ∀ {ℓ ℓRel ℓCode ℓR₁ ℓR₂ : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K O)
  → (P : Presentation {ℓR = ℓR₁} (codeView Pₒ))
  → (Q : Presentation {ℓR = ℓR₂} (codeView Pₒ))
  → CompletePresentation P
  → CompletePresentation Q
  → ∀ {x y}
  → Presentation._≼_ P x y ↔ Presentation._≼_ Q x y
boundaryObservationPresentationsAgree Pₒ = presentationsAgree

-- Observation-induced partiality:
-- given an explicit observation port on the *output boundary* into a lifted
-- interface, any kernel morphism becomes a genuinely partial map on code.
kernelHomToObservedPartialMap
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (V : View (Con (bnd K')) (LiftCP O))
  → (monoV : MonoMap (bnd K') (LiftCP O) (μ V))
  → KernelHom K K'
  → PM.PartialMap (CodePreorder K) O
kernelHomToObservedPartialMap {K = K} {K' = K'} {O = O} V monoV h =
  record
    { map = λ γ → μ V (decode K' (mapCode h γ))
    ; mono = mono
    }
  where
    mono
      : ∀ {γ δ}
      → _⊑_ (CodePreorder K) γ δ
      → _⊑_ (LiftCP O)
          (μ V (decode K' (mapCode h γ)))
          (μ V (decode K' (mapCode h δ)))
    mono {γ} {δ} γ⊑δ
      =
      let
        lawγ = decode-mapCode h γ
        lawδ = decode-mapCode h δ
      in
      transLiftCP
        {CP = O}
        {a = μ V (decode K' (mapCode h γ))}
        {b = μ V (LogOS.LT.Hom.map∂ h (decode K γ))}
        {c = μ V (decode K' (mapCode h δ))}
        (monoV (fst lawγ))
        (transLiftCP
          {CP = O}
          {a = μ V (LogOS.LT.Hom.map∂ h (decode K γ))}
          {b = μ V (LogOS.LT.Hom.map∂ h (decode K δ))}
          {c = μ V (decode K' (mapCode h δ))}
          (monoV (map∂-mono h γ⊑δ))
          (monoV (snd lawδ)))

observedCodeView
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → BoundaryObservationPort K' O
  → KernelHom K K'
  → View (Code K) (LiftCP O)
observedCodeView {K' = K'} Pₒ h =
  record { μ = λ γ → μ (boundaryView Pₒ) (decode K' (mapCode h γ)) }

observedSemantics
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → BoundaryObservationPort K' O
  → KernelHom K K'
  → Code K → Con (LiftCP O)
observedSemantics {K' = K'} Pₒ h γ =
  μ (boundaryView Pₒ) (decode K' (mapCode h γ))

observedPartialMap
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → BoundaryObservationPort K' O
  → KernelHom K K'
  → PM.PartialMap (CodePreorder K) O
observedPartialMap Pₒ =
  kernelHomToObservedPartialMap (boundaryView Pₒ) (boundaryView-mono Pₒ)

observedPartialMapTransport
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → {f g : KernelHom K K'}
  → LogOS.LT.Hom._⇒∂_ {K = K} {K' = K'} f g
  → ∀ γ
  → _⊑_ (LiftCP O)
      (PM.map (observedPartialMap Pₒ f) γ)
      (PM.map (observedPartialMap Pₒ g) γ)
observedPartialMapTransport Pₒ {f} {g} fg γ =
  boundaryView-mono Pₒ (⇒∂→⇒ {f = f} {g = g} fg γ)

canonicalObservedPresentation
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → Presentation (observedCodeView Pₒ h)
canonicalObservedPresentation Pₒ h = canonicalPresentation (observedCodeView Pₒ h)

canonicalObservedComplete
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → CompletePresentation (canonicalObservedPresentation Pₒ h)
canonicalObservedComplete Pₒ h = canonicalComplete (observedCodeView Pₒ h)

observedCanonicalFullAbstraction
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → ∀ {x y}
  → Presentation._≼_ (canonicalObservedPresentation Pₒ h) x y
    ↔ _⊑_ (LiftCP O)
        (observedSemantics Pₒ h x)
        (observedSemantics Pₒ h y)
observedCanonicalFullAbstraction Pₒ h =
  presentation↔canonical
    (canonicalObservedPresentation Pₒ h)
    (canonicalObservedComplete Pₒ h)

observedFullAbstraction
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → (P : Presentation {ℓR = ℓR} (observedCodeView Pₒ h))
  → CompletePresentation P
  → ∀ {x y}
  → Presentation._≼_ P x y
    ↔
    _⊑_ (LiftCP O)
      (observedSemantics Pₒ h x)
      (observedSemantics Pₒ h y)
observedFullAbstraction Pₒ h P CP =
  presentation↔canonical P CP

observedEquivFullAbstraction
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → (P : Presentation {ℓR = ℓR} (observedCodeView Pₒ h))
  → CompletePresentation P
  → ∀ {x y}
  → _≈_ (Presentation.CP P) x y
    ↔
    _≈_ (LiftCP O)
      (observedSemantics Pₒ h x)
      (observedSemantics Pₒ h y)
observedEquivFullAbstraction Pₒ h P CP =
  let
    fa = observedFullAbstraction Pₒ h P CP
  in
  intro
    (λ where
      (xy , yx) → (to fa xy , to fa yx))
    (λ where
      (xy , yx) → (from fa xy , from fa yx))

observedPresentation↔partialMap
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → (P : Presentation {ℓR = ℓR} (observedCodeView Pₒ h))
  → CompletePresentation P
  → ∀ {x y}
  → Presentation._≼_ P x y
    ↔
    _⊑_ (LiftCP O)
      (PM.map (observedPartialMap Pₒ h) x)
      (PM.map (observedPartialMap Pₒ h) y)
observedPresentation↔partialMap Pₒ h =
  observedFullAbstraction Pₒ h

observedCodePresentationsAgree
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR₁ ℓR₂ : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → (P : Presentation {ℓR = ℓR₁} (observedCodeView Pₒ h))
  → (Q : Presentation {ℓR = ℓR₂} (observedCodeView Pₒ h))
  → CompletePresentation P
  → CompletePresentation Q
  → ∀ {x y}
  → Presentation._≼_ P x y ↔ Presentation._≼_ Q x y
observedCodePresentationsAgree Pₒ h = presentationsAgree

observedPartialityCanonicality
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR₁ ℓR₂ : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → (P : Presentation {ℓR = ℓR₁} (observedCodeView Pₒ h))
  → (Q : Presentation {ℓR = ℓR₂} (observedCodeView Pₒ h))
  → CompletePresentation P
  → CompletePresentation Q
  → ∀ {x y}
  → Presentation._≼_ P x y ↔ Presentation._≼_ Q x y
observedPartialityCanonicality = observedCodePresentationsAgree

record CompleteObservedPresentationPackage
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  {O : ConPreorder ℓCode ℓRel}
  (Pₒ : BoundaryObservationPort K' O)
  (h : KernelHom K K')
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓCode')) where
  field
    presentation : Presentation {ℓR = ℓRel} (observedCodeView Pₒ h)
    completeOnObservedImage
      : ∀ {x y}
      → Presentation._≼_ presentation x y
        ↔
        _⊑_ (LiftCP O) (observedSemantics Pₒ h x) (observedSemantics Pₒ h y)

open CompleteObservedPresentationPackage public

record CompleteObservedPresentationsEquivalent
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  {O : ConPreorder ℓCode ℓRel}
  {Pₒ : BoundaryObservationPort K' O}
  {h : KernelHom K K'}
  (X Y : CompleteObservedPresentationPackage Pₒ h)
  : Set (ℓCode ⊔ ℓRel) where
  constructor mkCompleteObservedPresentationsEquivalent
  field
    agreeAt
      : ∀ {x y}
      → Presentation._≼_ (presentation X) x y
        ↔
        Presentation._≼_ (presentation Y) x y

open CompleteObservedPresentationsEquivalent public

CompleteObservedPresentationPackage≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
    {Pₒ : BoundaryObservationPort K' O}
    {h : KernelHom K K'}
  → CompleteObservedPresentationPackage Pₒ h
  → CompleteObservedPresentationPackage Pₒ h
  → Set (ℓCode ⊔ ℓRel)
CompleteObservedPresentationPackage≈ X Y =
  CompleteObservedPresentationsEquivalent X Y

completeObservedPresentationPackage≈-sym
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {K' : Kernel ℓ ℓRel ℓCode'}
      {O : ConPreorder ℓCode ℓRel}
      {Pₒ : BoundaryObservationPort K' O}
      {h : KernelHom K K'}
      {X Y : CompleteObservedPresentationPackage Pₒ h}
  → CompleteObservedPresentationPackage≈ X Y
  → CompleteObservedPresentationPackage≈ Y X
completeObservedPresentationPackage≈-sym
  {X = X}
  {Y = Y}
  XY =
  mkCompleteObservedPresentationsEquivalent
    (λ {x} {y} →
      intro
        (from (agreeAt XY {x} {y}))
        (to (agreeAt XY {x} {y})))

completeObservedPresentationPackage≈-trans
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {K' : Kernel ℓ ℓRel ℓCode'}
      {O : ConPreorder ℓCode ℓRel}
      {Pₒ : BoundaryObservationPort K' O}
      {h : KernelHom K K'}
      {X Y Z : CompleteObservedPresentationPackage Pₒ h}
  → CompleteObservedPresentationPackage≈ X Y
  → CompleteObservedPresentationPackage≈ Y Z
  → CompleteObservedPresentationPackage≈ X Z
completeObservedPresentationPackage≈-trans
  {X = X}
  {Y = Y}
  {Z = Z}
  XY
  YZ =
  mkCompleteObservedPresentationsEquivalent
    (λ {x} {y} →
      intro
        (λ px≤ →
          to (agreeAt YZ {x} {y})
            (to (agreeAt XY {x} {y}) px≤))
        (λ rx≤ →
          from (agreeAt XY {x} {y})
            (from (agreeAt YZ {x} {y}) rx≤)))

canonicalCompleteObservedPresentationPackage
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → CompleteObservedPresentationPackage Pₒ h
canonicalCompleteObservedPresentationPackage Pₒ h =
  record
    { presentation = canonicalObservedPresentation Pₒ h
    ; completeOnObservedImage = observedCanonicalFullAbstraction Pₒ h
    }

completeObservedPresentationCenter
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → CompleteObservedPresentationPackage Pₒ h
completeObservedPresentationCenter = canonicalCompleteObservedPresentationPackage

completeObservedPresentationFiber
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → ContractibleFiber
      (CompleteObservedPresentationPackage Pₒ h)
      (CompleteObservedPresentationPackage≈ {Pₒ = Pₒ} {h = h})
completeObservedPresentationFiber Pₒ h =
  Centering.mkContractibleFiber
    (completeObservedPresentationPackage≈-sym {Pₒ = Pₒ} {h = h})
    (completeObservedPresentationPackage≈-trans {Pₒ = Pₒ} {h = h})
    (canonicalCompleteObservedPresentationPackage Pₒ h)
    (λ pkg →
        mkCompleteObservedPresentationsEquivalent
          (λ {x} {y} →
            ↔-trans
              (completeOnObservedImage pkg {x} {y})
              (↔-sym (observedCanonicalFullAbstraction Pₒ h {x} {y}))))

completeObservedPresentationNoFork
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → NoSemanticFork (CompleteObservedPresentationPackage≈ {Pₒ = Pₒ} {h = h})
completeObservedPresentationNoFork Pₒ h =
  Centering.contractible⇒noSemanticFork (completeObservedPresentationFiber Pₒ h)

-- A structural functor `LOG → Par`:
-- objects are kernels seen as their induced code preorders,
-- morphisms are kernel morphisms seen as total partial maps on code.
codeToPar
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (LOG {ℓ} {ℓRel} {ℓCode})
      (PM.Par {ℓCon = ℓCode} {ℓRel = ℓRel})
codeToPar {ℓ} {ℓRel} {ℓCode} =
  let
    module S = Thin2Cat (LOG {ℓ} {ℓRel} {ℓCode})
    module T = Thin2Cat (PM.Par {ℓCon = ℓCode} {ℓRel = ℓRel})
  in
  record
    { mapObj = λ K → CodePreorder K
    ; mapHom = λ {A} {B} h → kernelHomToPartialMap {K = A} {K' = B} h
    ; mapHom-mono = λ {A} {B} {f} {g} le γ → ⇒∂→⇒ {K = A} {K' = B} {f = f} {g = g} le γ
    ; id-pres = λ {A} →
        ( (λ γ → refl⊑ (LiftCP (CodePreorder A)))
        , (λ γ → refl⊑ (LiftCP (CodePreorder A)))
        )
    ; comp-pres = λ {A} {B} {C} f g →
        ( (λ γ → refl⊑ (LiftCP (CodePreorder C)))
        , (λ γ → refl⊑ (LiftCP (CodePreorder C)))
        )
    }

-- Optional lift through the Grothendieck/Σ-totalisation of “tracked” partial maps
-- (refinement inherited from the base; displayed evidence ignored):
-- given an explicit indexing ledger (`ParTuringLedger`), every `Par` morphism
-- is decorated with its chosen tracker.
codeToParTracked
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (L : ParT.ParTuringLedger {ℓCon = ℓCode} {ℓRel = ℓRel})
  → Thin2Functor
      (LOG {ℓ} {ℓRel} {ℓCode})
      (Tracked.ParTracked (ParT.U L) (ParT.TU L))
codeToParTracked {ℓ} {ℓRel} {ℓCode} L =
  Tracked.trackPar (ParT.U L) (ParT.TU L)
    ∘F
  codeToPar {ℓ} {ℓRel} {ℓCode}
