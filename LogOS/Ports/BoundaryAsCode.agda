{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.BoundaryAsCode where

-- Canonical “denotational” presentation for dependent local boundaries.
--
-- This is the canonical dependent boundary-as-code presentation:
-- the shared boundary is `LocalBoundary I O`, where the local
-- observation preorder may vary with the index (`O : I → ConPreorder … …`).
--
-- The core pattern is unchanged:
-- - boundary-as-code kernel: code = boundary constraints, decode = identity;
-- - any dependent locality port denotes into it via its combined observation;
-- - boundary-transparent denotations are unique up to the chosen boundary
--   transport and observational equivalence (`≈`), not `≡` of code maps.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_; ≈-sym; idMonoMap; refl⊑)
import LogOS.LT.ConPreorder as CP
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Kernel using (Kernel; decode; BoundaryKernel; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts; mapCode)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.Syntax.Prop using (_↔_; intro; to; from)
open import LogOS.LT.Theorems.Centering as Centering using (ContractibleFiber; NoSemanticFork)
open import LogOS.Ports.Locality.Core using
  ( LocalityPort
  ; LocalBoundary
  ; localKernel
  )
open import LogOS.Ports.Locality.Lifts using (pointwiseClosure; pointwise≡→≈LocalBoundary)
open import LogOS.Ports.BoundaryTransparency using
  ( BoundaryTransparent
  ; decode-mapCode-transparent
  ; transportCon
  ; untransportCon
  ; untransport-decode-mapCode-transparent≈
  ; idBoundaryTransparent
  )

-- The boundary carrier (the combined observation space).
BoundaryCode
  : ∀ {ℓI ℓOCon ℓORel}
    (I : Set ℓI)
    (O : I → ConPreorder ℓOCon ℓORel)
  → Set (ℓI ⊔ ℓOCon)
BoundaryCode I O = Con (LocalBoundary I O)

-- Boundary as a dependent locality port: at region `i`, observe by evaluation at `i`.
boundaryPort
  : ∀ {ℓI ℓOCon ℓORel}
    (I : Set ℓI)
    (O : I → ConPreorder ℓOCon ℓORel)
  → LocalityPort (BoundaryCode I O) I O
boundaryPort I O =
  record
    { localProbe = λ i → record { μ = λ F → F i } }

-- The corresponding kernel (its decode is judgmental identity after unfolding `BoundaryKernel`).
boundaryKernel
  : ∀ {ℓI ℓOCon ℓORel}
    (I : Set ℓI)
    (O : I → ConPreorder ℓOCon ℓORel)
  → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) (ℓI ⊔ ℓOCon)
boundaryKernel I O = BoundaryKernel (LocalBoundary I O)

-- Any dependent local model canonically denotes into the boundary-as-code kernel.
denote
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → KernelHom (localKernel P) (boundaryKernel I O)
denote {I = I} {O = O} P =
  mkKernelHomParts
    (record
      { map∂ = λ c → c
      ; map∂-mono = idMonoMap {CP = LocalBoundary I O}
      })
    (record
      { mapCode = decode (localKernel P)
      ; decode-mapCode = λ _ → pointwise≡→≈LocalBoundary {I = I} {O = O} (λ _ → refl)
      })

-- In the shared-closure / distributed-semantics discipline, denotation is
-- automatically flow-preserving: boundary map is the identity.
denoteFlow
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (GC₀ : (i : I) → GuardedClosure (O i))
  → (P : LocalityPort X I O)
  → KernelHomFlow
      (pointwiseClosure {I = I} {O = O} GC₀)
      (pointwiseClosure {I = I} {O = O} GC₀)
      (denote P)
denoteFlow {I = I} {O = O} GC₀ P =
  record { preserves-Flow = λ _ → refl⊑ (LocalBoundary I O) }

decodeDenotation
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (decodeₓ : X → Con (LocalBoundary I O))
  → KernelHom
      (record
        { bnd = LocalBoundary I O
        ; Code = X
        ; decode = decodeₓ
        })
      (boundaryKernel I O)
decodeDenotation {I = I} {O = O} decodeₓ =
  mkKernelHomParts
    (record
      { map∂ = λ c → c
      ; map∂-mono = idMonoMap {CP = LocalBoundary I O}
      })
    (record
      { mapCode = decodeₓ
      ; decode-mapCode =
          λ _ → pointwise≡→≈LocalBoundary {I = I} {O = O} (λ _ → refl)
      })

-- --------------------------------------------------------------------------
-- Uniqueness: boundary-transparent adapters into the denotation are forced.

denoteBoundaryTransparent
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → BoundaryTransparent (denote P)
denoteBoundaryTransparent {I = I} {O = O} P =
  record
    { bnd≡ = refl
    ; map∂-transparent≈ =
        λ c → pointwise≡→≈LocalBoundary {I = I} {O = O} (λ _ → refl)
    }

transparent-mapCode≈decode
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent yo)
  → ∀ x
  → _≈_ (LocalBoundary I O)
      (mapCode yo x)
      (transportCon bt (decode (localKernel P) x))
transparent-mapCode≈decode _ _ bt x =
  decode-mapCode-transparent bt x

transparent-mapCode-normalised≈decode
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent yo)
  → ∀ x
  → _≈_ (LocalBoundary I O)
      (untransportCon bt (mapCode yo x))
      (decode (localKernel P) x)
transparent-mapCode-normalised≈decode _ _ bt x =
  untransport-decode-mapCode-transparent≈ bt x

transparentDenotation≈denote
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent yo)
  → ∀ x
  → _≈_ (LocalBoundary I O)
      (untransportCon bt (mapCode yo x))
      (mapCode (denote P) x)
transparentDenotation≈denote P yo bt x =
  transparent-mapCode-normalised≈decode P yo bt x

normalisedTransparentCode
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent yo)
  → X → Con (LocalBoundary I O)
normalisedTransparentCode _ yo bt x =
  untransportCon bt (mapCode yo x)

transparentDenotation↔localCodePreorder
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent yo)
  → ∀ {x y}
  → (CP._⊑_ (LocalBoundary I O)
       (normalisedTransparentCode P yo bt x)
       (normalisedTransparentCode P yo bt y))
    ↔
    (CP._⊑_ (CodePreorder (localKernel P)) x y)
transparentDenotation↔localCodePreorder {I = I} {O = O} P yo bt {x} {y} =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (LocalBoundary I O)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)

    x≈denote = transparentDenotation≈denote {I = I} {O = O} P yo bt x
    y≈denote = transparentDenotation≈denote {I = I} {O = O} P yo bt y
  in
  intro
    (λ xy →
      begin⊑
        decode (localKernel P) x
          ⊑⟨ snd x≈denote ⟩
        normalisedTransparentCode P yo bt x
          ⊑⟨ xy ⟩
        normalisedTransparentCode P yo bt y
          ⊑⟨ fst y≈denote ⟩
        decode (localKernel P) y
      ∎⊑)
    (λ xy →
      begin⊑
        normalisedTransparentCode P yo bt x
          ⊑⟨ fst x≈denote ⟩
        decode (localKernel P) x
          ⊑⟨ xy ⟩
        decode (localKernel P) y
          ⊑⟨ snd y≈denote ⟩
        normalisedTransparentCode P yo bt y
      ∎⊑)

transparentDenotation≈localCodePreorder
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent yo)
  → ∀ {x y}
  → (CP._≈_ (LocalBoundary I O)
       (normalisedTransparentCode P yo bt x)
       (normalisedTransparentCode P yo bt y))
    ↔
    (CP._≈_ (CodePreorder (localKernel P)) x y)
transparentDenotation≈localCodePreorder P yo bt =
  let
    classify = transparentDenotation↔localCodePreorder P yo bt
  in
  intro
    (λ where
      (xy , yx) → (to classify xy , to classify yx))
    (λ where
      (xy , yx) → (from classify xy , from classify yx))

transparent-mapCode-unique≈
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo₁ yo₂ : KernelHom (localKernel P) (boundaryKernel I O))
  → (bt₁ : BoundaryTransparent yo₁)
  → (bt₂ : BoundaryTransparent yo₂)
  → ∀ x
  → _≈_ (LocalBoundary I O)
      (untransportCon bt₁ (mapCode yo₁ x))
      (untransportCon bt₂ (mapCode yo₂ x))
transparent-mapCode-unique≈
  {I = I} {O = O} P yo₁ yo₂ bt₁ bt₂ x =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (LocalBoundary I O)
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)
  in
  begin≈
    untransportCon bt₁ (mapCode yo₁ x)
      ≈⟨ transparent-mapCode-normalised≈decode {I = I} {O = O} P yo₁ bt₁ x ⟩
    decode (localKernel P) x
      ≈⟨ ≈-sym {CP = LocalBoundary I O}
            (transparent-mapCode-normalised≈decode {I = I} {O = O} P yo₂ bt₂ x) ⟩
    untransportCon bt₂ (mapCode yo₂ x) ∎≈

record TransparentDenotationPackage
  {ℓX ℓI ℓOCon ℓORel : Level}
  {I : Set ℓI}
  {O : I → ConPreorder ℓOCon ℓORel}
  {X : Set ℓX}
  (P : LocalityPort X I O)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  constructor mkTransparentDenotationPackage
  field
    denotation : KernelHom (localKernel P) (boundaryKernel I O)
    transparent : BoundaryTransparent denotation

  normalisedCode : X → Con (LocalBoundary I O)
  normalisedCode = normalisedTransparentCode P denotation transparent

open TransparentDenotationPackage public

record TransparentDenotationPackage≈
  {ℓX ℓI ℓOCon ℓORel : Level}
  {I : Set ℓI}
  {O : I → ConPreorder ℓOCon ℓORel}
  {X : Set ℓX}
  {P : LocalityPort X I O}
  (A B : TransparentDenotationPackage P)
  : Set (ℓX ⊔ ℓI ⊔ ℓORel) where
  constructor mkTransparentDenotationPackage≈
  field
    agreeAt
      : ∀ x
      → _≈_ (LocalBoundary I O)
          (normalisedCode A x)
          (normalisedCode B x)

open TransparentDenotationPackage≈ public

transparentDenotationPackage≈-sym'
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
      {I : Set ℓI}
      {O : I → ConPreorder ℓOCon ℓORel}
      {X : Set ℓX}
      {P : LocalityPort X I O}
  → (A B : TransparentDenotationPackage P)
  → TransparentDenotationPackage≈ A B
  → TransparentDenotationPackage≈ B A
transparentDenotationPackage≈-sym' {I = I} {O = O} A B AB =
  mkTransparentDenotationPackage≈
    (λ x → CP.≈-sym {CP = LocalBoundary I O} (agreeAt AB x))

transparentDenotationPackage≈-sym
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
      {I : Set ℓI}
      {O : I → ConPreorder ℓOCon ℓORel}
      {X : Set ℓX}
      {P : LocalityPort X I O}
      {A B : TransparentDenotationPackage P}
  → TransparentDenotationPackage≈ A B
  → TransparentDenotationPackage≈ B A
transparentDenotationPackage≈-sym {A = A} {B = B} =
  transparentDenotationPackage≈-sym' A B

transparentDenotationPackage≈-trans'
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
      {I : Set ℓI}
      {O : I → ConPreorder ℓOCon ℓORel}
      {X : Set ℓX}
      {P : LocalityPort X I O}
  → (A B C : TransparentDenotationPackage P)
  → TransparentDenotationPackage≈ A B
  → TransparentDenotationPackage≈ B C
  → TransparentDenotationPackage≈ A C
transparentDenotationPackage≈-trans'
  {I = I}
  {O = O}
  A
  B
  C
  AB
  BC =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (LocalBoundary I O)
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)
  in
  mkTransparentDenotationPackage≈
    (λ x →
      begin≈
        normalisedCode A x
          ≈⟨ agreeAt AB x ⟩
        normalisedCode B x
          ≈⟨ agreeAt BC x ⟩
        normalisedCode C x ∎≈)

transparentDenotationPackage≈-trans
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
      {I : Set ℓI}
      {O : I → ConPreorder ℓOCon ℓORel}
      {X : Set ℓX}
      {P : LocalityPort X I O}
      {A B C : TransparentDenotationPackage P}
  → TransparentDenotationPackage≈ A B
  → TransparentDenotationPackage≈ B C
  → TransparentDenotationPackage≈ A C
transparentDenotationPackage≈-trans {A = A} {B = B} {C = C} =
  transparentDenotationPackage≈-trans' A B C

canonicalTransparentDenotationPackage
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → TransparentDenotationPackage P
canonicalTransparentDenotationPackage P =
  mkTransparentDenotationPackage (denote P) (denoteBoundaryTransparent P)

transparentDenotationCenter
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → TransparentDenotationPackage P
transparentDenotationCenter = canonicalTransparentDenotationPackage

transparentDenotationFiber
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → ContractibleFiber
      (TransparentDenotationPackage P)
      TransparentDenotationPackage≈
transparentDenotationFiber {I = I} {O = O} P =
  Centering.mkContractibleFiber
    (transparentDenotationPackage≈-sym {I = I} {O = O} {P = P})
    (transparentDenotationPackage≈-trans {I = I} {O = O} {P = P})
    (canonicalTransparentDenotationPackage P)
    (λ where
      pkg →
        mkTransparentDenotationPackage≈
          (λ x →
            transparent-mapCode-unique≈
              P
              (denotation pkg)
              (denote P)
              (transparent pkg)
              (denoteBoundaryTransparent P)
              x))

transparentDenotationNoFork
  : ∀ {ℓX ℓI ℓOCon ℓORel : Level}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → NoSemanticFork (TransparentDenotationPackage≈ {P = P})
transparentDenotationNoFork P =
  Centering.contractible⇒noSemanticFork (transparentDenotationFiber P)
