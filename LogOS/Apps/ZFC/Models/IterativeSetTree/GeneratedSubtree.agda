{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.GeneratedSubtree where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.LT.Presentation.GeneratedSubobject.Core as Gen

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST

-- Generated subtree of an iterative tree from a small classifier on its
-- existing children. This stays at the raw presentation level: no quotient,
-- no late collapse, only index filtering.
--
-- The exported LT data here is intentionally strict/equality-shaped. ZFC-side
-- refinement-first instantiations are obtained later by applying the canonical
-- LT adapters under explicit extensional-collapse assumptions.

strictLocalGeneratorsᵛ
  : ∀ {ℓ}
  → Gen.StrictLocalGenerators (IST.V {ℓ}) IST._∈ᵛ_ ℓ
strictLocalGeneratorsᵛ =
  record
    { Ix = IST.Idx
    ; elemAt = IST.elemAt
    ; memberIn = IST.memberIn
    ; memberOut = IST.memberOut
    }

generateSubtree
  : ∀ {ℓ}
  → (x : IST.V {ℓ})
  → (IST.Idx x → Set ℓ)
  → IST.V {ℓ}
generateSubtree (IST.sup I f) Q = IST.sup (Σ I Q) (λ { (i , _) → f i })

intoGeneratedSubtree
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (Q : IST.Idx x → Set ℓ)
  → (i : IST.Idx x)
  → Q i
  → z ≡ IST.elemAt x i
  → z IST.∈ᵛ generateSubtree x Q
intoGeneratedSubtree {x = IST.sup I f} Q i qi eq = (i , qi) , eq

outOfGeneratedSubtree
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (Q : IST.Idx x → Set ℓ)
  → z IST.∈ᵛ generateSubtree x Q
  → Σ (IST.Idx x) (λ i → Q i × (z ≡ IST.elemAt x i))
outOfGeneratedSubtree {x = IST.sup I f} Q ((i , qi) , eq) = i , (qi , eq)

strictGeneratedSubtreesᵛ
  : ∀ {ℓ}
  → Gen.StrictGeneratedSubobjects (strictLocalGeneratorsᵛ {ℓ}) ℓ
strictGeneratedSubtreesᵛ =
  record
    { generate = generateSubtree
    ; intoGenerated = intoGeneratedSubtree
    ; outOfGenerated = outOfGeneratedSubtree
    }

module Impl {ℓ : Level} = Gen.StrictFor (strictLocalGeneratorsᵛ {ℓ}) (strictGeneratedSubtreesᵛ {ℓ})

filterᵛ
  : ∀ {ℓ}
  → (x : IST.V {ℓ})
  → (IST.Idx x → Set ℓ)
  → IST.V {ℓ}
filterᵛ {ℓ} = Gen.StrictGeneratedSubobjects.generate (strictGeneratedSubtreesᵛ {ℓ})

filter-memberIn
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (Q : IST.Idx x → Set ℓ)
  → (i : IST.Idx x)
  → Q i
  → z ≡ IST.elemAt x i
  → z IST.∈ᵛ filterᵛ x Q
filter-memberIn {ℓ} = Gen.StrictGeneratedSubobjects.intoGenerated (strictGeneratedSubtreesᵛ {ℓ})

filter-memberOut
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (Q : IST.Idx x → Set ℓ)
  → z IST.∈ᵛ filterᵛ x Q
  → Σ (IST.Idx x) (λ i → Q i × (z ≡ IST.elemAt x i))
filter-memberOut {ℓ} = Gen.StrictGeneratedSubobjects.outOfGenerated (strictGeneratedSubtreesᵛ {ℓ})

filter-spec
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (Q : IST.Idx x → Set ℓ)
  → (z IST.∈ᵛ filterᵛ x Q)
      ↔ Σ (IST.Idx x) (λ i → Q i × (z ≡ IST.elemAt x i))
filter-spec = Impl.generated-spec
