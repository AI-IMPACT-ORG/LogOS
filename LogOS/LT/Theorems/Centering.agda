{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.Centering where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Generic center-contraction schema (refinement-level).
--
-- This captures the shared backbone behind:
-- - contractible candidate spaces (uniqueness up to refinement),
-- - cone path-independence,
-- - context-indexed approximation (budget/time/scale readings).
--
-- The theorem shape is intentionally minimal:
-- given symmetry/transitivity of a relation and two contractions to the same
-- center, path-independence follows.

open import LogOS.Prelude
import LogOS.LT.ConPreorder as ConPreorder
import LogOS.LT.ConPreorder.Indexed as IndexedConPreorder

-- ============================================================================
-- Non-indexed centering
-- ============================================================================

-- Contractible fiber: one canonical center plus the minimal “up-to” structure
-- needed for path-independence/no-fork reasoning.
--
-- Terminology note:
-- we avoid calling this an “equivalence relation” because we do not assume
-- reflexivity separately; symmetry+transitivity are the only properties used
-- by the centering spine (reflexivity can be derived once you have a
-- contraction to a center).
record ContractibleFiber
  {ℓA ℓ≈ : Level}
  (A : Set ℓA)
  (_≈_ : A → A → Set ℓ≈)
  : Set (lsuc (ℓA ⊔ ℓ≈)) where
  field
    sym≈
      : ∀ {x y}
      → _≈_ x y
      → _≈_ y x

    trans≈
      : ∀ {x y z}
      → _≈_ x y
      → _≈_ y z
      → _≈_ x z

    center : A
    contract : ∀ x → _≈_ x center

open ContractibleFiber public
mkContractibleFiber
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    {_≈_ : A → A → Set ℓ≈}
  → (sym≈ : ∀ {x y} → _≈_ x y → _≈_ y x)
  → (trans≈ : ∀ {x y z} → _≈_ x y → _≈_ y z → _≈_ x z)
  → (center : A)
  → (contract : ∀ x → _≈_ x center)
  → ContractibleFiber A _≈_
mkContractibleFiber sym≈ trans≈ center contract =
  record
    { sym≈ = sym≈
    ; trans≈ = trans≈
    ; center = center
    ; contract = contract
    }

mkConPreorderContractibleFiber
  : ∀ {ℓCon ℓRel}
    (CP : ConPreorder.ConPreorder ℓCon ℓRel)
  → (center : ConPreorder.Con CP)
  → (contract : ∀ x → ConPreorder._≈_ CP x center)
  → ContractibleFiber (ConPreorder.Con CP) (ConPreorder._≈_ CP)
mkConPreorderContractibleFiber CP center contract =
  mkContractibleFiber
    (ConPreorder.≈-sym {CP = CP})
    (λ {x} {y} {z} xy yz →
      let
        module R = LogOS.Prelude.RefinementKit.Reasoning CP
      in
      R._≈⟨_⟩_ x xy yz)
    center
    contract

confluent
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    {_≈_ : A → A → Set ℓ≈}
  → (F : ContractibleFiber A _≈_)
  → ∀ {x y}
  → _≈_ x y
confluent F {x} {y} =
  trans≈ F (contract F x) (sym≈ F (contract F y))

PathIndependence
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    (_≈_ : A → A → Set ℓ≈)
  → Set (ℓA ⊔ ℓ≈)
PathIndependence _≈_ = ∀ {x y} → _≈_ x y

NoSemanticFork
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    (_≈_ : A → A → Set ℓ≈)
  → Set (ℓA ⊔ ℓ≈)
NoSemanticFork = PathIndependence

contractible⇒path-independence
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    {_≈_ : A → A → Set ℓ≈}
  → ContractibleFiber A _≈_
  → PathIndependence _≈_
contractible⇒path-independence = confluent

path-independence⇒noSemanticFork
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    {_≈_ : A → A → Set ℓ≈}
  → PathIndependence _≈_
  → NoSemanticFork _≈_
path-independence⇒noSemanticFork P = P

contractible⇒noSemanticFork
  : ∀ {ℓA ℓ≈}
    {A : Set ℓA}
    {_≈_ : A → A → Set ℓ≈}
  → ContractibleFiber A _≈_
  → NoSemanticFork _≈_
contractible⇒noSemanticFork F {x} {y} =
  contractible⇒path-independence F {x = x} {y = y}
-- ============================================================================
-- Indexed centering (budget/context-indexed “up-to” relations)
-- ============================================================================

record IndexedContractibleFiber
  {ℓI ℓA ℓ≈ : Level}
  (Index : Set ℓI)
  (A : Set ℓA)
  (_≈_ : Index → A → A → Set ℓ≈)
  : Set (lsuc (ℓI ⊔ ℓA ⊔ ℓ≈)) where
  field
    symAt
      : ∀ {i x y}
      → _≈_ i x y
      → _≈_ i y x

    transAt
      : ∀ {i x y z}
      → _≈_ i x y
      → _≈_ i y z
      → _≈_ i x z

    center : A
    contract : ∀ i x → _≈_ i x center

open IndexedContractibleFiber public
mkIndexedContractibleFiber
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → (symAt : ∀ {i x y} → _≈_ i x y → _≈_ i y x)
  → (transAt : ∀ {i x y z} → _≈_ i x y → _≈_ i y z → _≈_ i x z)
  → (center : A)
  → (contract : ∀ i x → _≈_ i x center)
  → IndexedContractibleFiber Index A _≈_
mkIndexedContractibleFiber symAt transAt center contract =
  record
    { symAt = symAt
    ; transAt = transAt
    ; center = center
    ; contract = contract
    }

mkIndexedConPreorderContractibleFiber
  : ∀ {ℓI ℓA ℓRel}
    {Index : Set ℓI}
    {A : Set ℓA}
  → (ICP : IndexedConPreorder.IndexedConPreorder Index A ℓRel)
  → (center : A)
  → (contract : ∀ i x → IndexedConPreorder._≈_ ICP i x center)
  → IndexedContractibleFiber Index A (IndexedConPreorder._≈_ ICP)
mkIndexedConPreorderContractibleFiber ICP center contract =
  mkIndexedContractibleFiber
    (IndexedConPreorder.≈-symAt ICP)
    (IndexedConPreorder.≈-transAt ICP)
    center
    contract

indexedConfluent
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → (F : IndexedContractibleFiber Index A _≈_)
  → (i : Index)
  → ∀ {x y}
  → _≈_ i x y
indexedConfluent F i {x} {y} =
  transAt F (contract F i x) (symAt F (contract F i y))

IndexedPathIndependence
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
  → (_≈_ : Index → A → A → Set ℓ≈)
  → Set (ℓI ⊔ ℓA ⊔ ℓ≈)
IndexedPathIndependence _≈_ = ∀ i {x y} → _≈_ i x y

IndexedNoSemanticFork
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
  → (_≈_ : Index → A → A → Set ℓ≈)
  → Set (ℓI ⊔ ℓA ⊔ ℓ≈)
IndexedNoSemanticFork = IndexedPathIndependence

indexedContractible⇒path-independence
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → IndexedContractibleFiber Index A _≈_
  → IndexedPathIndependence _≈_
indexedContractible⇒path-independence F i {x} {y} =
  indexedConfluent F i {x = x} {y = y}

indexedContractible⇒noSemanticFork
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → IndexedContractibleFiber Index A _≈_
  → IndexedNoSemanticFork _≈_
indexedContractible⇒noSemanticFork =
  indexedContractible⇒path-independence

indexedContractible⇒confluentAt
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → (F : IndexedContractibleFiber Index A _≈_)
  → (i : Index)
  → ∀ {x y}
  → _≈_ i x y
indexedContractible⇒confluentAt = indexedConfluent

indexedContractible⇒pathIndependenceAt
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → (F : IndexedContractibleFiber Index A _≈_)
  → (i : Index)
  → ∀ {x y}
  → _≈_ i x y
indexedContractible⇒pathIndependenceAt = indexedContractible⇒path-independence

indexedContractible⇒noSemanticForkAt
  : ∀ {ℓI ℓA ℓ≈}
    {Index : Set ℓI}
    {A : Set ℓA}
    {_≈_ : Index → A → A → Set ℓ≈}
  → (F : IndexedContractibleFiber Index A _≈_)
  → (i : Index)
  → ∀ {x y}
  → _≈_ i x y
indexedContractible⇒noSemanticForkAt = indexedContractible⇒noSemanticFork
