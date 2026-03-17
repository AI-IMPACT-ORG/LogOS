{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Contracts where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Contracts and satisfaction (design-target spec v5.8, §6).
--
-- This module is *derived*: it adds no new kernel axioms.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder as Con using (ConPreorder; Con; _⊑_; refl⊑)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; mapCode; map∂-mono; decode-mapCode; _∘_; idKernelHom)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- --------------------------------------------------------------------------
-- Satisfaction (code satisfies a boundary constraint).

infix 3 _⊨_[_]
_⊨_[_] : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) → Code K → Con (bnd K) → Set ℓRel
K ⊨ γ [ c ] = _⊑_ (bnd K) c (decode K γ)

-- Satisfaction is preserved under kernel morphisms.

models-map
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → ∀ {γ c}
  → K ⊨ γ [ c ]
  → K' ⊨ mapCode h γ [ map∂ h c ]
models-map {K = K} {K' = K'} h {γ} {c} sat =
  let
    module R = ≤-Reasoning (bnd K')
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    (_ , mapDecode≤decodeMap) = decode-mapCode h γ
  in
  begin⊑
    map∂ h c
      ⊑⟨ map∂-mono h sat ⟩
    map∂ h (decode K γ)
      ⊑⟨ mapDecode≤decodeMap ⟩
    decode K' (mapCode h γ)
  ∎⊑

-- Satisfaction preservation for a *contract morphism* is ensured by a single
-- law inequality (see `ContractLaw` below).

-- --------------------------------------------------------------------------
ContractΣ : ∀ {ℓ ℓRel ℓCode} → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
ContractΣ {ℓ} {ℓRel} {ℓCode} = Σ (Kernel ℓ ℓRel ℓCode) (λ K → Con (bnd K))

record ContractR {ℓ ℓRel ℓCode : Level} : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where
  constructor mkContract
  field
    kernel   : Kernel ℓ ℓRel ℓCode
    contract : Con (bnd kernel)

open ContractR public
toΣ : ∀ {ℓ ℓRel ℓCode} → ContractR {ℓ} {ℓRel} {ℓCode} → ContractΣ {ℓ} {ℓRel} {ℓCode}
toΣ X = kernel X , contract X

fromΣ : ∀ {ℓ ℓRel ℓCode} → ContractΣ {ℓ} {ℓRel} {ℓCode} → ContractR {ℓ} {ℓRel} {ℓCode}
fromΣ (K , c) = mkContract K c

Contract : ∀ {ℓ ℓRel ℓCode} → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
Contract {ℓ} {ℓRel} {ℓCode} = ContractR {ℓ} {ℓRel} {ℓCode}

KernelOf : ∀ {ℓ ℓRel ℓCode} → Contract {ℓ} {ℓRel} {ℓCode} → Kernel ℓ ℓRel ℓCode
KernelOf = kernel

ConOf : ∀ {ℓ ℓRel ℓCode} (X : Contract {ℓ} {ℓRel} {ℓCode}) → Con (bnd (KernelOf X))
ConOf = contract

-- Contract morphisms (LOG∂, satisfaction-preserving).
--
-- A morphism `mkContract K c -> mkContract K' c'` is a kernel morphism
-- `h : K -> K'` such that
-- satisfaction transports from c to c' (via decoded observation):
--
--   c' ⊑ map∂ h c
--
-- This direction is forced by the polarity and the satisfaction definition
--   K ⊨ γ [ c ]  :⇔  c ⊑ decode γ.

ContractLaw
  : ∀ {ℓ ℓRel ℓCode}
  → (X Y : Contract {ℓ} {ℓRel} {ℓCode})
  → KernelHom (KernelOf X) (KernelOf Y)
  → Set ℓRel
ContractLaw X Y h = _⊑_ (bnd (KernelOf Y)) (ConOf Y) (map∂ h (ConOf X))

ContractHom
  : ∀ {ℓ ℓRel ℓCode}
  → (X Y : Contract {ℓ} {ℓRel} {ℓCode})
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
-- Level alignment: `Lift` matches the hom-level of `LOG` without changing content.
ContractHom {ℓ} {ℓRel} {ℓCode} X Y =
  Lift (lsuc ℓCode) (Σ (KernelHom (KernelOf X) (KernelOf Y)) (ContractLaw X Y))

hom
  : ∀ {ℓ ℓRel ℓCode} {X Y : Contract {ℓ} {ℓRel} {ℓCode}}
  → ContractHom X Y → KernelHom (KernelOf X) (KernelOf Y)
hom (lift (h , _)) = h

compat
  : ∀ {ℓ ℓRel ℓCode} {X Y : Contract {ℓ} {ℓRel} {ℓCode}} (f : ContractHom X Y)
  → ContractLaw X Y (hom f)
compat (lift (_ , p)) = p

idContractHom : ∀ {ℓ ℓRel ℓCode} (X : Contract {ℓ} {ℓRel} {ℓCode}) → ContractHom X X
idContractHom X =
  lift
    ( idKernelHom (KernelOf X)
    , refl⊑ (bnd (KernelOf X))
    )

infixr 40 _∘Contract_
_∘Contract_
  : ∀ {ℓ ℓRel ℓCode} {X Y Z : Contract {ℓ} {ℓRel} {ℓCode}}
  → ContractHom Y Z
  → ContractHom X Y
  → ContractHom X Z
_∘Contract_ {X = X} {Y = Y} {Z = Z} g f =
  let
    module R = ≤-Reasoning (bnd (KernelOf Z))
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  lift
    ( hom g ∘ hom f
    , (begin⊑
         ConOf Z ⊑⟨ compat g ⟩
         map∂ (hom g) (ConOf Y) ⊑⟨ map∂-mono (hom g) (compat f) ⟩
         map∂ (hom g) (map∂ (hom f) (ConOf X)) ∎⊑)
    )

-- If X --h--> Y satisfies the contract law, then satisfaction transports from
-- X’s contract to Y’s contract.

models-map-contract
  : ∀ {ℓ ℓRel ℓCode} {X Y : Contract {ℓ} {ℓRel} {ℓCode}}
  → (h : ContractHom X Y)
  → ∀ {γ}
  → KernelOf X ⊨ γ [ ConOf X ]
  → KernelOf Y ⊨ mapCode (hom h) γ [ ConOf Y ]
models-map-contract {X = X} {Y = Y} h {γ} sat =
  let
    module R = ≤-Reasoning (bnd (KernelOf Y))
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    ( ConOf Y ⊑⟨ compat h ⟩
      map∂ (hom h) (ConOf X) ⊑⟨ models-map (hom h) {γ = γ} {c = ConOf X} sat ⟩
      decode (KernelOf Y) (mapCode (hom h) γ) ∎⊑ )

-- Contract preorder: reachability by existence of a satisfaction-preserving contract morphism.

ContractPreorder : ∀ {ℓ ℓRel ℓCode} → ConPreorder (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
ContractPreorder {ℓ} {ℓRel} {ℓCode} =
  record
    { Con   = Contract {ℓ} {ℓRel} {ℓCode}
    ; _⊑_   = ContractHom
    ; refl  = λ {X} → idContractHom X
    ; trans = λ {X} {Y} {Z} f g → g ∘Contract f
    }
