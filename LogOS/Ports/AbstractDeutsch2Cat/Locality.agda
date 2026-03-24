{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat.Locality where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( Con
  ; MonoMap
  ; idMonoMap
  ; ≡→≈
  ; refl⊑
  ; _≈_
  )
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using
  ( KernelHom
  ; mkKernelHomParts
  ; idKernelHom
  ; map∂
  ; mapCode
  ; map∂-mono
  ; decode-mapCode
  )
  renaming (_∘_ to _∘k_)
open import LogOS.LT.Thin2Cat using (Thin2Cat; PullbackThin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; forgetPullbackThin2Functor; _∘F_)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedHom
  ; mkTotalObjR
  ; mkTotalHomR
  ; base
  ; baseHom
  ; dispHom
  )

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
open import LogOS.Ports.Locality.Core using (LocalityPort)
open import LogOS.Ports.PhysicalTransformers using
  ( pointwiseEndoMap
  ; pointwiseEndoMap-mono
  ; mkKernelHomPointwise
  )
import LogOS.Ports.LawSlice2Cat as LawSlice
import LogOS.LT.Ports.PortSig as PortSig

private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  open DependentLocalSemantics PS
  -- ------------------------------------------------------------------------
  -- Physical kernels, and the locality-restricted physical 2-category.

  record PhysicalKernel : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓCode)) where
    field
      Code   : Set ℓCode
      decode : Code → Con Bnd

  open PhysicalKernel public
  kernel : PhysicalKernel → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓCode
  kernel K =
    record
      { bnd = Bnd
      ; Code = Code K
      ; decode = decode K
      }

  -- Base: physical kernels with arbitrary kernel morphisms.
  --
-- This is LOG, pulled back along `kernel : PhysicalKernel → Kernel …`.
  LOGᵏ
    : Thin2Cat
        (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓCode))
        (lsuc (ℓI ⊔ ℓOCon) ⊔ lsuc (ℓI ⊔ ℓORel) ⊔ ℓCode)
        (ℓCode ⊔ (ℓI ⊔ ℓORel))
  LOGᵏ =
    PullbackThin2Cat
      {C = LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode}}
      PhysicalKernel
      kernel

  -- Displayed restriction: locality-preserving boundary action.
  --
  -- A physical morphism is a kernel morphism together with a chosen pointwise
  -- boundary action `mapAt`, and a coherence up to mutual refinement (`≈`)
  -- identifying the base boundary map with the pointwise endomap.
  record LocalityAction {K K' : PhysicalKernel} (h : KernelHom (kernel K) (kernel K'))
    : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)) where
    field
      mapAt  : (i : I) → Con (O i) → Con (O i)
      monoAt : ∀ i → MonoMap (O i) (O i) (mapAt i)

      map∂-pointwise≈
        : ∀ c i
        → _≈_ (O i) (map∂ h c i) (mapAt i (c i))

  idLocalityAction
    : ∀ {K : PhysicalKernel}
    → LocalityAction (idKernelHom (kernel K))
  idLocalityAction =
    record
      { mapAt = λ _ x → x
      ; monoAt = λ i → idMonoMap {CP = O i}
      ; map∂-pointwise≈ = λ _ i → (refl⊑ (O i) , refl⊑ (O i))
      }

  compLocalityAction
    : ∀ {K₁ K₂ K₃ : PhysicalKernel}
      {f : KernelHom (kernel K₁) (kernel K₂)}
      {g : KernelHom (kernel K₂) (kernel K₃)}
    → LocalityAction f
    → LocalityAction g
    → LocalityAction (g ∘k f)
  compLocalityAction {f = f} {g = g} lf lg =
    record
      { mapAt = λ i x → LocalityAction.mapAt lg i (LocalityAction.mapAt lf i x)
      ; monoAt = λ i le →
          LocalityAction.monoAt lg i (LocalityAction.monoAt lf i le)
      ; map∂-pointwise≈ = map∂-pointwise-comp
      }
    where
      mapAtComp : (i : I) → Con (O i) → Con (O i)
      mapAtComp i x = LocalityAction.mapAt lg i (LocalityAction.mapAt lf i x)

      map∂-pointwise-comp
        : ∀ c i
        → _≈_ (O i) (map∂ (g ∘k f) c i) (mapAtComp i (c i))
      map∂-pointwise-comp c i =
        let
          module R = ≤-Reasoning (O i)
          open R using (begin≈_; _≈⟨_⟩_; _∎≈)

          eqG : _≈_ (O i) (map∂ g (map∂ f c) i) (LocalityAction.mapAt lg i (map∂ f c i))
          eqG = LocalityAction.map∂-pointwise≈ lg (map∂ f c) i

          eqF : _≈_ (O i) (map∂ f c i) (LocalityAction.mapAt lf i (c i))
          eqF = LocalityAction.map∂-pointwise≈ lf c i

          eqF' : _≈_ (O i)
                  (LocalityAction.mapAt lg i (map∂ f c i))
                  (LocalityAction.mapAt lg i (LocalityAction.mapAt lf i (c i)))
          eqF' =
            ( LocalityAction.monoAt lg i (fst eqF)
            , LocalityAction.monoAt lg i (snd eqF)
            )
        in
        begin≈
          map∂ g (map∂ f c) i ≈⟨ eqG ⟩
          LocalityAction.mapAt lg i (map∂ f c i) ≈⟨ eqF' ⟩
          LocalityAction.mapAt lg i (LocalityAction.mapAt lf i (c i)) ∎≈

  -- η-unit payload for the locality restriction layer (avoids Topℓ/⊤ footguns).
  record LocalityOb : Set where
    constructor ttLoc

  data LocalityTag : Set where
    localityTag : LocalityTag

  module Port =
    LawSlice.Exports
      {C = LOGᵏ}
      {Tag = LocalityTag}
      LocalityOb
      LocalityAction
      idLocalityAction
      compLocalityAction

  port2Cat
    : LawSlice.Singleton2Cat LOGᵏ LocalityTag
  port2Cat =
    Port.port2Cat

  open Port public using (singleton; stack; port; Displayed; WithPort; forget)

  -- The physical thin 2-category: Σ-decoration of the locality restriction.
  --
  -- Refinement between decorated morphisms is inherited from the underlying
  -- kernel morphism only; locality evidence is S-tier structure.

  -- Canonical embedding of a raw physical kernel into `LOGᵖ` objects.
  physicalObj : PhysicalKernel → Thin2Cat.Obj WithPort
  physicalObj K = mkTotalObjR K ttLoc

  -- Physical morphisms between raw kernels (convenience alias).
  PhysicalHom
    : PhysicalKernel → PhysicalKernel
    → Set
        ( lsuc (ℓI ⊔ ℓOCon)
        ⊔ lsuc (ℓI ⊔ ℓORel)
        ⊔ ℓCode
        ⊔ lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)
        )
  PhysicalHom K K' = DecoratedHom Displayed (physicalObj K) (physicalObj K')

  -- Canonical constructor: build a physical morphism from pointwise data.
  mkPhysicalHom
    : ∀ {K K' : PhysicalKernel}
    → (mapAt : (i : I) → Con (O i) → Con (O i))
    → (monoAt : ∀ i → MonoMap (O i) (O i) (mapAt i))
    → (mapCode : Code K → Code K')
    → (decode-mapCode
        : ∀ γ
        → _≈_ Bnd
            (decode K' (mapCode γ))
            (pointwiseEndoMap {I = I} {O = O} mapAt (decode K γ)))
    → PhysicalHom K K'
  mkPhysicalHom {K} {K'} mapAt monoAt mapCode decode-mapCode =
    mkTotalHomR
      h
      (record
        { mapAt = mapAt
        ; monoAt = monoAt
        ; map∂-pointwise≈ = λ _ i → (refl⊑ (O i) , refl⊑ (O i))
        })
    where
      h : KernelHom (kernel K) (kernel K')
      h = mkKernelHomPointwise localityPort localityPort' mapAt monoAt mapCode decode-mapCode
        where
          localityPort : LocalityPort (Code K) I O
          localityPort =
            record
              { localProbe = λ i → record { μ = λ γ → decode K γ i } }

          localityPort' : LocalityPort (Code K') I O
          localityPort' =
            record
              { localProbe = λ i → record { μ = λ γ → decode K' γ i } }

  module Strict where
    -- Strict-input wrapper: accept definitional decode coherence and lift it.
    mkPhysicalHom≡
      : ∀ {K K' : PhysicalKernel}
      → (mapAt : (i : I) → Con (O i) → Con (O i))
      → (monoAt : ∀ i → MonoMap (O i) (O i) (mapAt i))
      → (mapCode : Code K → Code K')
      → (decode-mapCode
          : ∀ γ
          → decode K' (mapCode γ)
            ≡
            pointwiseEndoMap {I = I} {O = O} mapAt (decode K γ))
      → PhysicalHom K K'
    mkPhysicalHom≡ {K = K} {K' = K'} mapAt monoAt mapCode decode-mapCode =
      mkPhysicalHom
        {K = K} {K' = K'}
        mapAt
        monoAt
        mapCode
        (λ γ → ≡→≈ {CP = Bnd} (decode-mapCode γ))

  idPhysicalHom : ∀ (K : PhysicalKernel) → PhysicalHom K K
  idPhysicalHom K =
    mkPhysicalHom
      {K = K} {K' = K}
      (λ _ x → x)
      (λ i → idMonoMap {CP = O i})
      (λ γ → γ)
      (λ _ → (refl⊑ Bnd , refl⊑ Bnd))

  infixr 40 _∘p_
  _∘p_
    : ∀ {K₁ K₂ K₃ : PhysicalKernel}
    → PhysicalHom K₂ K₃
    → PhysicalHom K₁ K₂
    → PhysicalHom K₁ K₃
  _∘p_ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g f =
    Thin2Cat._∘_ WithPort {A = physicalObj K₁} {B = physicalObj K₂} {C = physicalObj K₃} g f

  -- Underlying physical kernel of a locality-decorated object.
  physicalKernelOf : Thin2Cat.Obj WithPort → PhysicalKernel
  physicalKernelOf X = base {D = Displayed} X

  -- Underlying kernel morphism of a physical morphism.
  physicalToKernelHom
    : ∀ {A B : Thin2Cat.Obj WithPort}
    → Con (Thin2Cat.Hom WithPort A B)
    → KernelHom (kernel (physicalKernelOf A))
      (kernel (physicalKernelOf B))
  physicalToKernelHom {A} {B} f =
    baseHom {D = Displayed} {X = A} {Y = B} f

  -- Locality evidence for a physical morphism.
  physicalLocalityAction
    : ∀ {A B : Thin2Cat.Obj WithPort}
    → (f : Con (Thin2Cat.Hom WithPort A B))
    → LocalityAction (physicalToKernelHom f)
  physicalLocalityAction {A} {B} f =
    dispHom {D = Displayed} {X = A} {Y = B} f

  physicalMapAt
    : ∀ {A B : Thin2Cat.Obj WithPort}
    → Con (Thin2Cat.Hom WithPort A B)
    → (i : I) → Con (O i) → Con (O i)
  physicalMapAt f = LocalityAction.mapAt (physicalLocalityAction f)

  physicalMonoAt
    : ∀ {A B : Thin2Cat.Obj WithPort}
    → (f : Con (Thin2Cat.Hom WithPort A B))
    → (∀ i → MonoMap (O i) (O i) (physicalMapAt f i))
  physicalMonoAt f = LocalityAction.monoAt (physicalLocalityAction f)

  -- Forgetful functor LOGᵏ → LOG (forget the `PhysicalKernel` wrapper).
  forgetPhysicalKernel
    : Thin2Functor LOGᵏ (LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode})
  forgetPhysicalKernel = forgetPullbackThin2Functor PhysicalKernel kernel

  -- Forgetful 2-functor into the ambient LOG of kernels (fixed dependent boundary).
  forgetPhysical
    : Thin2Functor WithPort (LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode})
  forgetPhysical = forgetPhysicalKernel ∘F forget
