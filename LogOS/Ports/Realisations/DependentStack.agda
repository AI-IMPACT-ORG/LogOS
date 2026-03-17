{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Realisations.DependentStack where

-- One-boundary / many-realisations pattern (dependent-locality).
--
-- This module factors out the generic “shared dependent boundary + many code
-- types realising it” pattern used by multiple application packs.
--
-- Structure:
-- - choose a distributed semantics ledger `DependentLocalSemantics` (index `I`,
--   local observables `O`, local doctrines `GC₀`);
-- - present each “realisation” as a dependent locality port into the shared
--   boundary `Bnd = LocalBoundary I O`;
-- - assemble those ports into a `Stack` and derive `stackKernel` / `programKernel`;
-- - package refinement-first boundary transports as `LocalTranslation`,
-- - keep strict equality as an explicit opt-in under `Strict`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap; refl⊑; idMonoMap; ≡→≈)
open import LogOS.LT.Flow using (GuardedClosure; Flow; mono)
open import LogOS.LT.Kernel using (Kernel; decode)
open import LogOS.LT.Stack using (Stack; stackKernel; programKernel; opKernel)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _⇒∂_) renaming (_∘_ to _∘k_)
open import LogOS.LT.HomFlow using (KernelHomFlow)

open import LogOS.Ports.Locality.Core using
  ( LocalityPort
  ; localKernel
  ; localView
  )
open import LogOS.Ports.Locality.Lifts using (pointwise≡→≈LocalBoundary)
open import LogOS.Ports.PhysicalTransformers using
  ( pointwiseEndoMap
  ; pointwiseEndoMap-mono
  ; mkKernelHomFlow
  )
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- --------------------------------------------------------------------------
-- Realisation family: fill the record, derive the kernels.

record RealisationFamily
  {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
  (S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓOp ⊔ ℓCode)) where
  open DependentLocalSemantics S renaming (I to Iₛ; O to Oₛ; GC₀ to GC₀ₛ; Bnd to Bndₛ; GC to GCₛ)

  field
    Op    : Set ℓOp
    Code  : Op → Set ℓCode
    local : (o : Op) → LocalityPort (Code o) Iₛ Oₛ

  -- The resulting stack (one boundary, many views).
  stack : Stack {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓOp} {ℓCode}
  stack =
    record
      { bnd = Bndₛ
    ; Op = Op
    ; Code = Code
    ; op = λ o → localView (local o)
    }

  -- Derived kernels.
  StackK : Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) (ℓOp ⊔ ℓCode)
  StackK = stackKernel stack

  ProgramK : Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ((ℓI ⊔ ℓOCon) ⊔ (ℓI ⊔ ℓORel) ⊔ ℓOp ⊔ ℓCode)
  ProgramK = programKernel stack

  -- Each realisation is a kernel over the shared boundary.
  K : Op → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓCode
  K o = opKernel stack o

  -- Alternate spelling: dependent locality port → kernel.
  localK : Op → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓCode
  localK o = localKernel (local o)

open RealisationFamily public renaming
    ( Op to OpOf
    ; Code to CodeOf
    ; local to localOf
    ; stack to stackOf
    ; StackK to StackKOf
    ; ProgramK to ProgramKOf
    ; K to KOf
    ; localK to localKOf
    )

realisationKernel
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → (F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → OpOf F
  → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) ℓCode
realisationKernel F = KOf F

sharedBoundary
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S
  → ConPreorder (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel)
sharedBoundary {S = S} _ = DependentLocalSemantics.Bnd S

record BoundaryEndomapTransport
  {ℓI ℓOCon ℓORel : Level}
  (S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  open DependentLocalSemantics S renaming (I to Iₛ; O to Oₛ; GC₀ to GC₀ₛ)
  field
    mapAt
      : (i : Iₛ) → Con (Oₛ i) → Con (Oₛ i)

    monoAt
      : ∀ i → MonoMap (Oₛ i) (Oₛ i) (mapAt i)

    causalAt
      : ∀ i c
      → _⊑_ (Oₛ i) (mapAt i (Flow (GC₀ₛ i) c)) (Flow (GC₀ₛ i) (mapAt i c))

boundaryEndomapTransport-normalize
  : ∀ {ℓI ℓOCon ℓORel : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → (T : BoundaryEndomapTransport S)
  → (c : Con (DependentLocalSemantics.Bnd S))
  → (i : DependentLocalSemantics.I S)
  → _⊑_ (DependentLocalSemantics.O S i)
      (BoundaryEndomapTransport.mapAt T i
        (Flow (DependentLocalSemantics.GC₀ S i) (c i)))
      (Flow (DependentLocalSemantics.GC₀ S i)
        (BoundaryEndomapTransport.mapAt T i (c i)))
boundaryEndomapTransport-normalize T c i =
  BoundaryEndomapTransport.causalAt T i (c i)

boundaryEndomapTransport-compose
  : ∀ {ℓI ℓOCon ℓORel : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → BoundaryEndomapTransport S
  → BoundaryEndomapTransport S
  → BoundaryEndomapTransport S
boundaryEndomapTransport-compose {S = S} g f =
  record
    { mapAt = λ i c → BoundaryEndomapTransport.mapAt g i (BoundaryEndomapTransport.mapAt f i c)
    ; monoAt = λ i {x} {y} le →
        BoundaryEndomapTransport.monoAt g i
          (BoundaryEndomapTransport.monoAt f i le)
    ; causalAt = λ i c →
        let
          module R = ≤-Reasoning (Oₛ i)
          open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
        in
        begin⊑
          BoundaryEndomapTransport.mapAt g i
            (BoundaryEndomapTransport.mapAt f i (Flow (GC₀ₛ i) c))
            ⊑⟨ BoundaryEndomapTransport.monoAt g i
                 (BoundaryEndomapTransport.causalAt f i c) ⟩
          BoundaryEndomapTransport.mapAt g i
            (Flow (GC₀ₛ i) (BoundaryEndomapTransport.mapAt f i c))
            ⊑⟨ BoundaryEndomapTransport.causalAt g i
                 (BoundaryEndomapTransport.mapAt f i c) ⟩
          Flow (GC₀ₛ i)
            (BoundaryEndomapTransport.mapAt g i
              (BoundaryEndomapTransport.mapAt f i c)) ∎⊑
    }
  where
    open DependentLocalSemantics S renaming (O to Oₛ; GC₀ to GC₀ₛ)

idBoundaryEndomapTransport
  : ∀ {ℓI ℓOCon ℓORel : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → BoundaryEndomapTransport S
idBoundaryEndomapTransport {S = S} =
  record
    { mapAt = λ _ c → c
    ; monoAt = λ i → idMonoMap {CP = DependentLocalSemantics.O S i}
    ; causalAt = λ i _ → refl⊑ (DependentLocalSemantics.O S i)
    }

-- --------------------------------------------------------------------------
-- Refinement-first translation shape (dependent boundaries).
--
-- In dependent-local semantics the boundary carrier is function-shaped
-- `(i : I) → Con (O i)`, but the canonical comparison operator is the
-- boundary preorder `≈`. Strict equality of dependent functions is kept under
-- `Strict`.

record LocalTranslation
  {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
  {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  (F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  (o o' : OpOf F)
  : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓCode)) where
  open DependentLocalSemantics S renaming (I to Iₛ; O to Oₛ; GC₀ to GC₀ₛ; Bnd to Bndₛ)
  open RealisationFamily F
  field
    mapAt
      : (i : Iₛ) → Con (Oₛ i) → Con (Oₛ i)

    monoAt
      : ∀ i → MonoMap (Oₛ i) (Oₛ i) (mapAt i)

    causalAt
      : ∀ i c
      → _⊑_ (Oₛ i) (mapAt i (Flow (GC₀ₛ i) c)) (Flow (GC₀ₛ i) (mapAt i c))

    mapCode
      : Code o → Code o'

    decode-mapCode
      : ∀ γ
      → _≈_ Bndₛ
          (decode (K o') (mapCode γ))
          (pointwiseEndoMap {I = Iₛ} {O = Oₛ} mapAt (decode (K o) γ))

  decode-mapCodeAt≈
    : ∀ γ i
    → _≈_ (Oₛ i)
        (decode (K o') (mapCode γ) i)
        (pointwiseEndoMap {I = Iₛ} {O = Oₛ} mapAt (decode (K o) γ) i)
  decode-mapCodeAt≈ γ i =
    ( fst (decode-mapCode γ) i
    , snd (decode-mapCode γ) i
    )

  normalize-transportAt
    : ∀ γ i
    → _⊑_ (Oₛ i)
        (mapAt i (Flow (GC₀ₛ i) (decode (K o) γ i)))
        (Flow (GC₀ₛ i) (decode (K o') (mapCode γ) i))
  normalize-transportAt γ i =
    let
      module R = ≤-Reasoning (Oₛ i)
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    in
    begin⊑
      mapAt i (Flow (GC₀ₛ i) (decode (K o) γ i))
        ⊑⟨ causalAt i (decode (K o) γ i) ⟩
      Flow (GC₀ₛ i)
        (pointwiseEndoMap {I = Iₛ} {O = Oₛ} mapAt (decode (K o) γ) i)
        ⊑⟨ mono (GC₀ₛ i) (snd (decode-mapCodeAt≈ γ i)) ⟩
      Flow (GC₀ₛ i) (decode (K o') (mapCode γ) i) ∎⊑

open LocalTranslation public

localTranslationTransport
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
      {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
      {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
      {o o' : OpOf F}
  → LocalTranslation F o o'
  → BoundaryEndomapTransport S
localTranslationTransport T =
  record
    { mapAt = LocalTranslation.mapAt T
    ; monoAt = LocalTranslation.monoAt T
    ; causalAt = LocalTranslation.causalAt T
    }

idLocalTranslation
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
    (o : OpOf F)
  → LocalTranslation F o o
idLocalTranslation {S = S} F o =
  record
    { mapAt = BoundaryEndomapTransport.mapAt idTransport
    ; monoAt = BoundaryEndomapTransport.monoAt idTransport
    ; causalAt = BoundaryEndomapTransport.causalAt idTransport
    ; mapCode = λ γ → γ
    ; decode-mapCode = λ _ → (refl⊑ Bndₛ , refl⊑ Bndₛ)
    }
  where
    open DependentLocalSemantics S renaming (Bnd to Bndₛ)
    idTransport : BoundaryEndomapTransport S
    idTransport = idBoundaryEndomapTransport {S = S}

infixr 40 _∘LT_
_∘LT_
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
    {o₁ o₂ o₃ : OpOf F}
  → LocalTranslation F o₂ o₃
  → LocalTranslation F o₁ o₂
  → LocalTranslation F o₁ o₃
_∘LT_ {S = S} {F = F} {o₁ = o₁} {o₂ = o₂} {o₃ = o₃} g f =
  record
    { mapAt = λ i c → LocalTranslation.mapAt g i (LocalTranslation.mapAt f i c)
    ; monoAt = λ i {x} {y} le →
        LocalTranslation.monoAt g i (LocalTranslation.monoAt f i le)
    ; causalAt = λ i c →
        let
          module R = ≤-Reasoning (Oₛ i)
          open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
        in
        begin⊑
          LocalTranslation.mapAt g i (LocalTranslation.mapAt f i (Flow (GC₀ₛ i) c))
            ⊑⟨ LocalTranslation.monoAt g i (LocalTranslation.causalAt f i c) ⟩
          LocalTranslation.mapAt g i (Flow (GC₀ₛ i) (LocalTranslation.mapAt f i c))
            ⊑⟨ LocalTranslation.causalAt g i (LocalTranslation.mapAt f i c) ⟩
          Flow (GC₀ₛ i) (LocalTranslation.mapAt g i (LocalTranslation.mapAt f i c)) ∎⊑
    ; mapCode = λ γ → LocalTranslation.mapCode g (LocalTranslation.mapCode f γ)
    ; decode-mapCode = λ γ →
        let
          module R = ≤-Reasoning Bndₛ
          open R using (begin≈_; _≈⟨_⟩_; _∎≈)

          step-f
            : _≈_ Bndₛ
                (pointwiseEndoMap {I = Iₛ} {O = Oₛ} (LocalTranslation.mapAt g)
                  (decode (KOf F o₂) (LocalTranslation.mapCode f γ)))
                (pointwiseEndoMap {I = Iₛ} {O = Oₛ} (LocalTranslation.mapAt g)
                  (pointwiseEndoMap {I = Iₛ} {O = Oₛ} (LocalTranslation.mapAt f)
                    (decode (KOf F o₁) γ)))
          step-f =
            ( pointwiseEndoMap-mono
                {I = Iₛ} {O = Oₛ}
                (LocalTranslation.mapAt g)
                (LocalTranslation.monoAt g)
                (fst (LocalTranslation.decode-mapCode f γ))
            , pointwiseEndoMap-mono
                {I = Iₛ} {O = Oₛ}
                (LocalTranslation.mapAt g)
                (LocalTranslation.monoAt g)
                (snd (LocalTranslation.decode-mapCode f γ))
            )
        in
        begin≈
          decode (KOf F o₃) (LocalTranslation.mapCode g (LocalTranslation.mapCode f γ))
            ≈⟨ LocalTranslation.decode-mapCode g (LocalTranslation.mapCode f γ) ⟩
          pointwiseEndoMap {I = Iₛ} {O = Oₛ} (LocalTranslation.mapAt g)
            (decode (KOf F o₂) (LocalTranslation.mapCode f γ))
            ≈⟨ step-f ⟩
          pointwiseEndoMap {I = Iₛ} {O = Oₛ} (LocalTranslation.mapAt g)
            (pointwiseEndoMap {I = Iₛ} {O = Oₛ} (LocalTranslation.mapAt f)
              (decode (KOf F o₁) γ))
            ≈⟨ pointwise≡→≈LocalBoundary {I = Iₛ} {O = Oₛ} (λ _ → refl) ⟩
          pointwiseEndoMap
            {I = Iₛ} {O = Oₛ}
            (λ i c → LocalTranslation.mapAt g i (LocalTranslation.mapAt f i c))
            (decode (KOf F o₁) γ) ∎≈
    }
  where
    open DependentLocalSemantics S renaming (I to Iₛ; O to Oₛ; GC₀ to GC₀ₛ; Bnd to Bndₛ)

module Strict where
  record StrictLocalTranslation
    {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
    (o o' : OpOf F)
    : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓCode)) where
    open DependentLocalSemantics S renaming (I to Iₛ; O to Oₛ; GC₀ to GC₀ₛ)
    open RealisationFamily F
    field
      mapAt
        : (i : Iₛ) → Con (Oₛ i) → Con (Oₛ i)

      monoAt
        : ∀ i → MonoMap (Oₛ i) (Oₛ i) (mapAt i)

      causalAt
        : ∀ i c
        → _⊑_ (Oₛ i) (mapAt i (Flow (GC₀ₛ i) c)) (Flow (GC₀ₛ i) (mapAt i c))

      mapCode
        : Code o → Code o'

      decode-mapCode
        : ∀ γ
        → decode (K o') (mapCode γ)
          ≡
          pointwiseEndoMap {I = Iₛ} {O = Oₛ} mapAt (decode (K o) γ)

  open StrictLocalTranslation public

forgetStrict
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
    {o o' : OpOf F}
  → Strict.StrictLocalTranslation F o o'
  → LocalTranslation F o o'
forgetStrict {S = S} t =
  record
    { mapAt = Strict.StrictLocalTranslation.mapAt t
    ; monoAt = Strict.StrictLocalTranslation.monoAt t
    ; causalAt = Strict.StrictLocalTranslation.causalAt t
    ; mapCode = Strict.StrictLocalTranslation.mapCode t
    ; decode-mapCode = λ γ → ≡→≈ {CP = DependentLocalSemantics.Bnd S} (Strict.StrictLocalTranslation.decode-mapCode t γ)
    }

-- Assemble the local data into a certified flow-preserving kernel morphism.
toKernelHomFlow
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
    {o o' : OpOf F}
  → LocalTranslation F o o'
  → Σ
      (KernelHom (KOf F o) (KOf F o'))
      (λ h → KernelHomFlow (DependentLocalSemantics.GC S) (DependentLocalSemantics.GC S) h)
toKernelHomFlow {S = S} {F = F} {o = o} {o' = o'} t =
  mkKernelHomFlow
    (DependentLocalSemantics.GC₀ S)
    (localOf F o)
    (localOf F o')
    (mapAt t)
    (monoAt t)
    (causalAt t)
    (mapCode t)
    (decode-mapCode t)

toKernelHom
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
    {o o' : OpOf F}
  → LocalTranslation F o o'
  → KernelHom (KOf F o) (KOf F o')
toKernelHom t = proj₁ (toKernelHomFlow t)

kernelHomFromLocalTranslation
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
    {o o' : OpOf F}
  → LocalTranslation F o o'
  → Σ
      (KernelHom (KOf F o) (KOf F o'))
      (λ h → KernelHomFlow (DependentLocalSemantics.GC S) (DependentLocalSemantics.GC S) h)
kernelHomFromLocalTranslation = toKernelHomFlow

-- Behavioural equality of kernel homs: mutual observational refinement.
-- (By default: the boundary-driven refinement `_⇒∂_` used by base `LOG`.)
--
-- This is the appropriate notion for signals/guardrails: `KernelHom` carries
-- proof-relevant coherence data, so definitional equality of the whole record
-- is brittle and not stable under refactoring.
infix 4 _≈ₖ_
_≈ₖ_
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom K K' → KernelHom K K' → Set (ℓCode ⊔ ℓRel)
f ≈ₖ g = (f ⇒∂ g) × (g ⇒∂ f)

toKernelHom-id
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
    (o : OpOf F)
  → toKernelHom (idLocalTranslation F o) ≈ₖ idKernelHom (KOf F o)
toKernelHom-id {S = S} _ _ =
  ( (λ _ → refl⊑ (DependentLocalSemantics.Bnd S))
  , (λ _ → refl⊑ (DependentLocalSemantics.Bnd S))
  )

toKernelHom-comp
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    {F : RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S}
    {o₁ o₂ o₃ : OpOf F}
    (g : LocalTranslation F o₂ o₃)
    (f : LocalTranslation F o₁ o₂)
  → toKernelHom (g ∘LT f) ≈ₖ toKernelHom g ∘k toKernelHom f
toKernelHom-comp {S = S} _ _ =
  ( (λ _ → refl⊑ (DependentLocalSemantics.Bnd S))
  , (λ _ → refl⊑ (DependentLocalSemantics.Bnd S))
  )
