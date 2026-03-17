{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.PredicateReindexing where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Predicate-fiber reindexing fragment.
--
-- The boundary fiber `bnd : Kernel → ConPreorder` can be viewed as a space of
-- predicates/constraints “over” a kernel boundary.
--
-- This is deliberately only the reindexing fragment:
-- - no quantifiers (Σ/Π), no Beck–Chevalley,
-- - no comprehension, and no fibrational cleavage interface.
-- Hyperdoctrine language is therefore interpretive only.
--
-- Taking opposite fibers makes the Σ-decoration (category-of-elements-style; refinement inherited from the base) line up
-- definitionally with `ContractHom`:
--
--   objects  : mkContract K c
--   morphisms: h : K → K'  with  c' ⊑ map∂ h c
--
-- This is the category-of-elements-style perspective that makes the induced logic explicit:
-- contracts are predicates transported along translations.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; Opp; MonoMap)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; map∂-mono)
open import LogOS.LT.Contracts using (Contract; ContractHom; KernelOf; ConOf; hom; compat)

-- Boundary fiber, with polarity flipped.
bndᵒᵖ : ∀ {ℓ ℓRel ℓCode : Level} → Kernel ℓ ℓRel ℓCode → ConPreorder ℓ ℓRel
bndᵒᵖ K = Opp (bnd K)

-- Predicate-fiber alias: opposite boundary fiber over a kernel.
PredicateFiber : ∀ {ℓ ℓRel ℓCode : Level} → Kernel ℓ ℓRel ℓCode → ConPreorder ℓ ℓRel
PredicateFiber = bndᵒᵖ

-- The same underlying boundary map is monotone on opposite fibers.
map∂ᵒᵖ-mono
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → MonoMap (bndᵒᵖ K) (bndᵒᵖ K') (map∂ h)
map∂ᵒᵖ-mono h {x} {y} y⊑x = map∂-mono h y⊑x

-- Traditional name for `map∂` on opposite fibers.
reindex-mono
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → MonoMap (PredicateFiber K) (PredicateFiber K') (map∂ h)
reindex-mono = map∂ᵒᵖ-mono

-- Grothendieck-style spelling of a contract morphism (explicit fiber arrow).
--
-- In the opposite fiber, the morphism condition is:
--   map∂ h c ⊑ᵒᵖ c'
-- which is definitionally:
--   c' ⊑ map∂ h c
GrothendieckCondition
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (X Y : Contract {ℓ} {ℓRel} {ℓCode})
  → KernelHom (KernelOf X) (KernelOf Y)
  → Set ℓRel
GrothendieckCondition X Y h =
  _⊑_ (bndᵒᵖ (KernelOf Y)) (map∂ h (ConOf X)) (ConOf Y)

-- The key alignment lemma: the Grothendieck condition is exactly `compat`.
compat-isGrothendieck
  : ∀ {ℓ ℓRel ℓCode : Level} {X Y : Contract {ℓ} {ℓRel} {ℓCode}} (f : ContractHom X Y)
  → GrothendieckCondition X Y (hom f)
compat-isGrothendieck f = compat f
