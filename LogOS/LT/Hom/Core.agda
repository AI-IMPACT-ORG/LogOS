{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Hom.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder as Con using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; _≈_
  ; MonoMap
  )
open import LogOS.LT.FunPreorder using (FunPreorder)
open import LogOS.LT.View using (_⊑[_]_; ObsView; TransportView; mkRoleView; forget; μᵣ)
open import LogOS.LT.Kernel using (Kernel; EncodePort; bnd; Code; decode; encode)
import LogOS.LT.Coherence as Coherence
import LogOS.LT.BoundaryHom as Boundary
import LogOS.LT.BoundaryImplementation.Core as Implementation

boundaryMap∂ = Boundary.BoundaryHom.map∂
boundaryMap∂-mono = Boundary.BoundaryHom.map∂-mono

-- Kernel morphisms are the stable façade over the architecture/implementation
-- split:
-- - architecture: boundary transport (`BoundaryHom`)
-- - implementation: a chosen code-level witness realises that transport
-- - law: further displayed doctrine layers may be stacked afterwards
--
-- Equality-valued coherence lives in `LogOS.LT.Hom.Strictification`, not here.
BoundaryImplementation = Implementation.BoundaryImplementation
implementCode = Implementation.implementCode
decode-implementsBoundary = Implementation.decode-implementsBoundary
idBoundaryImplementation = Implementation.idBoundaryImplementation
composeBoundaryImplementation = Implementation.composeBoundaryImplementation

record KernelHomLikeR
  (m : Coherence.CohMode)
  {ℓ ℓRel ℓCode ℓCode' : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (K' : Kernel ℓ ℓRel ℓCode')
  : Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓCode' ⊔ Coherence.CohLevel m ℓ ℓRel) where
  constructor mkKernelHomLikeR
  field
    boundary : Boundary.BoundaryHom K K'
    compat : BoundaryImplementation m boundary

KernelHomLike
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
  → (m : Coherence.CohMode) → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode'
  → Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓCode' ⊔ Coherence.CohLevel m ℓ ℓRel)
KernelHomLike m K K' = KernelHomLikeR m K K'

toKernelHomLikeR
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHomLike m K K'
  → KernelHomLikeR m K K'
toKernelHomLikeR h = h

fromKernelHomLikeR
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHomLikeR m K K'
  → KernelHomLike m K K'
fromKernelHomLikeR h = h

KernelHom≈ : ∀ {ℓ ℓRel ℓCode ℓCode'} → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode' → Set _
KernelHom≈ = KernelHomLike Coherence.approx

KernelHom⊑ : ∀ {ℓ ℓRel ℓCode ℓCode'} → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode' → Set _
KernelHom⊑ = KernelHomLike Coherence.under

-- Default public-facing coherence: mutual refinement (`≈`).
KernelHom : ∀ {ℓ ℓRel ℓCode ℓCode'} → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode' → Set _
KernelHom = KernelHom≈

BehavioralKernelHom
  : ∀ {ℓ ℓRel ℓCode ℓCode'} → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode' → Set _
BehavioralKernelHom = KernelHom

UnderApproxKernelHom
  : ∀ {ℓ ℓRel ℓCode ℓCode'} → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode' → Set _
UnderApproxKernelHom = KernelHom⊑

boundaryPart
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHomLikeR m K K'
  → Boundary.BoundaryHom K K'
boundaryPart = KernelHomLikeR.boundary

implementationPart
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHomLikeR m K K')
  → BoundaryImplementation m (boundaryPart h)
implementationPart = KernelHomLikeR.compat

mkKernelHomParts
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h∂ : Boundary.BoundaryHom K K')
  → BoundaryImplementation m h∂
  → KernelHomLikeR m K K'
mkKernelHomParts = mkKernelHomLikeR

-- Projections (keep stable names used across the repo).
map∂
  : ∀ {m ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHomLike m K K'
  → Con (bnd K) → Con (bnd K')
map∂ h = boundaryMap∂ (boundaryPart h)

map∂-mono
  : ∀ {m ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHomLike m K K')
  → MonoMap (bnd K) (bnd K') (map∂ h)
map∂-mono h = boundaryMap∂-mono (boundaryPart h)

mapCode
  : ∀ {m ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHomLike m K K'
  → Code K → Code K'
mapCode h = implementCode (implementationPart h)

decode-mapCode
  : ∀ {m ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (h : KernelHomLike m K K')
  → ∀ γ
  → Coherence.CohRel m (bnd K')
      (decode K' (mapCode h γ))
      (map∂ h (decode K γ))
decode-mapCode h = decode-implementsBoundary (implementationPart h)

decode-mapCode≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : BehavioralKernelHom K K')
  → ∀ γ
  → _≈_ (bnd K')
      (decode K' (mapCode h γ))
      (map∂ h (decode K γ))
decode-mapCode≈ = decode-mapCode

decode-mapCode⊑
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : UnderApproxKernelHom K K')
  → ∀ γ
  → _⊑_ (bnd K')
      (decode K' (mapCode h γ))
      (map∂ h (decode K γ))
decode-mapCode⊑ = decode-mapCode

-- Identity and composition (generic: all coherence modes).

idKernelHomLike
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode}
  → (K : Kernel ℓ ℓRel ℓCode)
  → KernelHomLike m K K
idKernelHomLike {m = m} K =
  mkKernelHomParts
    (Boundary.idBoundaryHom K)
    (idBoundaryImplementation {m = m} K)

infixr 40 _∘Like_
_∘Like_
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → KernelHomLike m K₂ K₃
  → KernelHomLike m K₁ K₂
  → KernelHomLike m K₁ K₃
_∘Like_ {m = m} {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g f =
  mkKernelHomParts
    (Boundary._∘∂_ (boundaryPart g) (boundaryPart f))
    (composeBoundaryImplementation {m = m} {K₁ = K₁} {K₂ = K₂} {K₃ = K₃}
      {f∂ = boundaryPart f} {g∂ = boundaryPart g}
      (implementationPart g)
      (implementationPart f))

-- Identity and composition (default coherence: `≈`).

idKernelHom : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) → KernelHom K K
idKernelHom K = idKernelHomLike {m = Coherence.approx} K

infixr 40 _∘_
_∘_
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → KernelHom K₂ K₃
  → KernelHom K₁ K₂
  → KernelHom K₁ K₃
_∘_ = _∘Like_ {m = Coherence.approx}

-- Decoded observation of kernel morphisms (pointwise, implementation-first picture).
--
-- This view is convenient for:
-- - presentation/“proof system” layers that compare adapters by running an implementation
--   (`mapCode`) and then decoding.
--
-- Note: base LOG uses the boundary-driven refinement (`transportView` / `⇒∂`)
-- so that 2-cells are definitionally insensitive to the choice of implementation.
-- The two pictures are equivalent up to pointwise `≈` (`obsView≈transportView`).
--
-- The boundary-only (implementation-insensitive) picture is `transportView`
-- (boundary transport). The two views are pointwise ≈-equivalent
-- (`obsView≈transportView`), hence induce equivalent pullback refinements
-- (`⇒→⇒∂` / `⇒∂→⇒`).

obs
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom K K'
  → Code K → Con (bnd K')
obs {K' = K'} h γ = decode K' (mapCode h γ)

obsView
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → ObsView (KernelHom K K') (FunPreorder (Code K) (bnd K'))
obsView {K = K} {K' = K'} =
  mkRoleView (record { μ = λ h γ → obs {K = K} {K' = K'} h γ })

-- Boundary-only observation transport (G-tier only; H-tier guards are encoded as boundary constraints):
-- transport what the observer sees, without inspecting the implementation (`mapCode`).

transportObs
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom K K'
  → Code K → Con (bnd K')
transportObs {K = K} h γ = map∂ h (decode K γ)

transportView
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → TransportView (KernelHom K K') (FunPreorder (Code K) (bnd K'))
transportView {K = K} {K' = K'} =
  mkRoleView (record { μ = λ h γ → transportObs {K = K} {K' = K'} h γ })

-- Basic “sandwich” projections of `decode-mapCode` (default coherence: `≈`).

obs⊑transport
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → ∀ γ
  → _⊑_ (bnd K') (obs h γ) (transportObs h γ)
obs⊑transport h γ = fst (decode-mapCode h γ)

transport⊑obs
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → ∀ γ
  → _⊑_ (bnd K') (transportObs h γ) (obs h γ)
transport⊑obs h γ = snd (decode-mapCode h γ)

-- Boundary-driven refinement between morphisms (pullback along `transportView`).
--
-- This is definitionally boundary-only (G-tier): it only inspects `map∂`.

infix 4 _⇒∂_
_⇒∂_
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom K K'
  → KernelHom K K'
  → Set (ℓCode ⊔ ℓRel)
_⇒∂_ {K = K} {K' = K'} f g = f ⊑[ forget (transportView {K = K} {K' = K'}) ] g

-- Bridge: the two “pictures” are pointwise observationally equivalent.
--
-- For each morphism `h`, running the chosen implementation and observing it (`obsView`)
-- agrees up to mutual refinement (`≈`) with transporting observation along the
-- boundary morphism (`transportView`).

obsView≈transportView
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → _≈_
      (FunPreorder (Code K) (bnd K'))
      (μᵣ (obsView {K = K} {K' = K'}) h)
      (μᵣ (transportView {K = K} {K' = K'}) h)
obsView≈transportView {K = K} {K' = K'} h =
  ( obs⊑transport {K = K} {K' = K'} h
  , transport⊑obs {K = K} {K' = K'} h
  )

-- 2-cells as observational refinements (pullback along `obsView`).
--
-- Equivalently: pullback along `transportView` (boundary-driven), since the two
-- views are pointwise ≈-equivalent. See `⇒→⇒∂` / `⇒∂→⇒`.

infix 4 _⇒_
_⇒_
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom K K'
  → KernelHom K K'
  → Set (ℓCode ⊔ ℓRel)
_⇒_ {K = K} {K' = K'} f g = f ⊑[ forget (obsView {K = K} {K' = K'}) ] g

-- Bridge: observational refinement is independent of which picture you pick.
--
-- This makes `obsView` “derived from” `transportView` in the only sense that
-- matters to the LT spine: they induce equivalent pullback refinements.

⇒→⇒∂
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {f g : KernelHom K K'}
  → f ⇒ g
  → f ⇒∂ g
⇒→⇒∂ {K' = K'} {f = f} {g = g} fg γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K')
  in
  R._⊑⟨_⟩_
    (transportObs f γ)
    (transport⊑obs f γ)
    (R._⊑⟨_⟩_ (obs f γ) (fg γ) (obs⊑transport g γ))

⇒∂→⇒
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {f g : KernelHom K K'}
  → f ⇒∂ g
  → f ⇒ g
⇒∂→⇒ {K' = K'} {f = f} {g = g} fg γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K')
  in
  R._⊑⟨_⟩_
    (obs f γ)
    (obs⊑transport f γ)
    (R._⊑⟨_⟩_ (transportObs f γ) (fg γ) (transport⊑obs g γ))

⇒↔⇒∂
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {f g : KernelHom K K'}
  → (f ⇒ g → f ⇒∂ g) × (f ⇒∂ g → f ⇒ g)
⇒↔⇒∂ {K = K} {K' = K'} {f = f} {g = g} =
  ( ⇒→⇒∂ {K = K} {K' = K'} {f = f} {g = g}
  , ⇒∂→⇒ {K = K} {K' = K'} {f = f} {g = g}
  )

-- Whiskering: composition is monotone in both arguments w.r.t. `_⇒_`.

whiskerL
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → (h : KernelHom K₂ K₃)
  → {f g : KernelHom K₁ K₂}
  → f ⇒ g
  → (h ∘ f) ⇒ (h ∘ g)
whiskerL {K₂ = K₂} {K₃ = K₃} h {f} {g} fg γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K₃)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)

    hF : _≈_ (bnd K₃)
          (decode K₃ (mapCode h (mapCode f γ)))
          (map∂ h (decode K₂ (mapCode f γ)))
    hF = decode-mapCode h (mapCode f γ)

    hG : _≈_ (bnd K₃)
          (decode K₃ (mapCode h (mapCode g γ)))
          (map∂ h (decode K₂ (mapCode g γ)))
    hG = decode-mapCode h (mapCode g γ)
  in
  begin⊑
    decode K₃ (mapCode h (mapCode f γ))
      ⊑⟨ fst hF ⟩
    map∂ h (decode K₂ (mapCode f γ))
      ⊑⟨ map∂-mono h (fg γ) ⟩
    map∂ h (decode K₂ (mapCode g γ))
      ⊑⟨ snd hG ⟩
    decode K₃ (mapCode h (mapCode g γ)) ∎⊑

whiskerR
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → {f g : KernelHom K₂ K₃}
  → (k : KernelHom K₁ K₂)
  → f ⇒ g
  → (f ∘ k) ⇒ (g ∘ k)
whiskerR k fg γ = fg (mapCode k γ)

-- Whiskering for the boundary-driven refinement `⇒∂` (derived).
--
-- These are not definitional consequences of `transportView`, but follow by
-- transporting monotonicity across the equivalence `⇒↔⇒∂`.

whiskerL∂
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → (h : KernelHom K₂ K₃)
  → {f g : KernelHom K₁ K₂}
  → f ⇒∂ g
  → (h ∘ f) ⇒∂ (h ∘ g)
whiskerL∂ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} h {f} {g} fg =
  ⇒→⇒∂
    {K = K₁} {K' = K₃}
    {f = h ∘ f} {g = h ∘ g}
    (whiskerL
      {K₁ = K₁} {K₂ = K₂} {K₃ = K₃}
      h
      {f = f} {g = g}
      (⇒∂→⇒ {K = K₁} {K' = K₂} {f = f} {g = g} fg))

whiskerR∂
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → {f g : KernelHom K₂ K₃}
  → (k : KernelHom K₁ K₂)
  → f ⇒∂ g
  → (f ∘ k) ⇒∂ (g ∘ k)
whiskerR∂ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f} {g} k fg =
  ⇒→⇒∂
    {K = K₁} {K' = K₃}
    {f = f ∘ k} {g = g ∘ k}
    (whiskerR
      {K₁ = K₁} {K₂ = K₂} {K₃ = K₃}
      {f = f} {g = g}
      k
      (⇒∂→⇒ {K = K₂} {K' = K₃} {f = f} {g = g} fg))
