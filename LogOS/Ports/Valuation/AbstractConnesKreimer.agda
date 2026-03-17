{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.AbstractConnesKreimer where

-- Connes–Kreimer, in refinement-first form.
--
-- This file is a *generalisation* of the usual Connes–Kreimer Hopf-algebra
-- presentation. It keeps the categorical shadow that LogOS can internalise
-- without committing to linear algebra or equality-level algebraic laws:
--
-- - diagrams: rooted trees / forests,
--   (here forests are *lists*, i.e. ordered; commutative variants can be added
--   later as an explicit quotient/opacity layer),
-- - “coproduct”: admissible cuts presented as a finitary *enumeration*,
-- - “convolution”: finite join (`⊔ᶠ`) as idempotent aggregation + multiplication (`·`)
--   into an arbitrary finite-join prequantale boundary,
-- - “scheme”: a closure on the target boundary (a `QuanticNucleus`, i.e. a `Flow`
--   preserving finite joins up to `≈` and laxly coherent with multiplication).
--
-- Non-goal: a full Hopf algebra development (coassociativity/antipode proofs) or
-- Birkhoff decomposition. Those require extra assumptions (e.g. Rota–Baxter
-- splitting) that are intentionally not part of the minimal LogOS kernel.
--
-- The result is a refinement-first, order-enriched CK *shadow* that can be
-- reused outside QFT (e.g. generic closure generation and self-consistent
-- resummation patterns).
--
-- Concrete payload: the structure needed to express:
--
-- - rooted trees / forests (diagram syntax),
-- - the admissible-cut coproduct (as a list of cut pairs), and
-- - convolution of “characters” into a finite-join prequantale boundary.
--
-- This is the barebones spine behind the Connes–Kreimer renormalisation
-- recursion; the renormalisation *scheme* is supplied separately as a
-- quantic nucleus / closure on the target boundary.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.List.Ops using (_++_; map; concatMap; _∈_; here; there)

open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; mkStable; elem)
open import LogOS.LT.Sup.FinSup using (FinSup)
open import LogOS.LT.Effectivity using (Effectivity)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.AbstractQuanticNucleus using (QuanticNucleus)
import LogOS.Ports.Valuation.AbstractQuanticNucleus as Nucleus

-- --------------------------------------------------------------------------
-- Minimal list surface: we reuse the prelude list ops module.

-- --------------------------------------------------------------------------
-- Rooted trees / forests.

data Tree {ℓP : Level} (P : Set ℓP) : Set ℓP where
  node : P → List (Tree P) → Tree P

Forest : ∀ {ℓP : Level} (P : Set ℓP) → Set ℓP
Forest P = List (Tree P)

-- --------------------------------------------------------------------------
-- Admissible cuts (coproduct combinatorics).
--
-- `edgeCuts t` enumerates admissible cuts of *edges* in the rooted tree `t`,
-- returning:
-- - `P` : the pruned forest (the “cut-off” subtrees), and
-- - `R` : the remaining trunk (still a tree containing the original root).
--
-- This includes the empty cut: `([] , t)`.
--
-- We also add the extra “root cut” separately when forming the Connes–Kreimer
-- coproduct: `t ⊗ 1` corresponds to `([ t ] , [])` at the forest level.

edgeCuts : ∀ {ℓP : Level} {P : Set ℓP} → Tree P → List (Forest P × Tree P)
edgeCuts {P = P} (node p children) =
  map (λ { (pruned , remChildren) → (pruned , node p remChildren) }) (combine children)
  where
    -- For each child subtree we can either:
    -- - cut the edge above it (remove it from the trunk, add it to the pruned forest), or
    -- - keep it, and cut inside it recursively.
    childOptions : Tree P → List (Forest P × Forest P)
    childOptions t =
      ((t ∷ []) , [])
      ∷
      map (λ { (pf , trunk) → (pf , (trunk ∷ [])) }) (edgeCuts t)

    -- Combine options across the list of children (cartesian product),
    -- concatenating the pruned forests and the remaining-child forests.
    combine : List (Tree P) → List (Forest P × Forest P)
    combine [] = ([] , []) ∷ []
    combine (t ∷ ts) =
      concatMap
        (λ { (pf₁ , rem₁) →
          map
            (λ { (pf₂ , rem₂) → (pf₁ ++ pf₂ , rem₁ ++ rem₂) })
            (combine ts)
        })
        (childOptions t)

-- Connes–Kreimer coproduct pairs, forest-level:
--   Δ(t) : List (P × R)
-- where both components are forests (unit is `[]`).
coproduct : ∀ {ℓP : Level} {P : Set ℓP} → Tree P → List (Forest P × Forest P)
coproduct t =
  ((t ∷ []) , [])
  ∷
  map (λ { (pf , trunk) → (pf , (trunk ∷ [])) }) (edgeCuts t)

-- --------------------------------------------------------------------------
-- Convolution into a join-prequantale target.

module CK
  {ℓCon ℓRel ℓP : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (JP : JoinPrequantale CP)
  (P : Set ℓP)
  where
  open JoinPrequantale JP
  open FinSup FS
  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  -- Finite join (idempotent aggregation) in the boundary semilattice.
  joinList : List (Con CP) → Con CP
  joinList [] = ⊥ᶠ
  joinList (x ∷ xs) = x ⊔ᶠ joinList xs

  map-∈
    : ∀ {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB}
      (f : A → B) {x : A} {xs : List A}
    → x ∈ xs
    → f x ∈ map f xs
  map-∈ f here = here
  map-∈ f (there x∈xs) = there (map-∈ f x∈xs)

  joinList-ub
    : ∀ {x : Con CP} {xs : List (Con CP)}
    → x ∈ xs
    → _⊑_ CP x (joinList xs)
  joinList-ub {x = x} {xs = y ∷ ys} here =
    ⊔ᶠ-ub₁ y (joinList ys)
  joinList-ub {x = x} {xs = y ∷ ys} (there x∈xs) =
    begin⊑
      x ⊑⟨ joinList-ub x∈xs ⟩
      joinList ys ⊑⟨ ⊔ᶠ-ub₂ y (joinList ys) ⟩
      (y ⊔ᶠ joinList ys) ∎⊑

  -- Extend a tree-evaluator multiplicatively to forests.
  forestEval : (Tree P → Con CP) → Forest P → Con CP
  forestEval φ [] = e
  forestEval φ (t ∷ ts) = φ t · forestEval φ ts

  -- Convolution defined by the cut coproduct.
  --
  -- Read as: finite join over all admissible cuts `(P , R)` of `t`,
  -- multiplying the “left” evaluation on the pruned forest with the “right”
  -- evaluation on the trunk forest.
  infixl 7 _⋆_
  _⋆_ : (Tree P → Con CP) → (Tree P → Con CP) → Tree P → Con CP
  (φ ⋆ ψ) t =
    joinList
      (map
        (λ { (pf , rf) → forestEval φ pf · forestEval ψ rf })
        (coproduct {P = P} t))

  -- Minimal “Feynman rules” interface: an insertion operator at each primitive.
  --
  -- Standard CK/DSE reading: `ins p` inserts a primitive divergence label `p`
  -- around a product of subdiagram evaluations.
  mutual
    evalTree : (P → Con CP → Con CP) → Tree P → Con CP
    evalTree ins (node p sub) = ins p (evalForest ins sub)

    evalForest : (P → Con CP → Con CP) → Forest P → Con CP
    evalForest ins [] = e
    evalForest ins (t ∷ ts) = evalTree ins t · evalForest ins ts

  -- A quantic nucleus provides the renormalisation scheme (closure on the
  -- target join-prequantale).
  schemeEffectivity : QuanticNucleus {CP = CP} JP → Effectivity CP
  schemeEffectivity N = record { GC = QuanticNucleus.GC N }

  renormalise : QuanticNucleus {CP = CP} JP → Con CP → Con CP
  renormalise N = Effectivity.normalize (schemeEffectivity N)

  renormaliseChar
    : QuanticNucleus {CP = CP} JP
    → (Tree P → Con CP)
    → Tree P → Con CP
  renormaliseChar N φ t = renormalise N (φ t)

  cutHead : Tree P → Forest P × Forest P
  cutHead t = ((t ∷ []) , [])

  cutTail : Tree P → List (Forest P × Forest P)
  cutTail t = map (λ { (pf , trunk) → (pf , (trunk ∷ [])) }) (edgeCuts t)

  stableForest
    : (N : QuanticNucleus {CP = CP} JP)
    → (Tree P → Con CP)
    → Forest P
    → Stable {CP = CP} (Flow (QuanticNucleus.GC N))
  stableForest N χ forest =
    mkStable
      (renormalise N (forestEval χ forest))
      (GuardedClosure.idemp-lax (QuanticNucleus.GC N) (forestEval χ forest))

  stableCut
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ ψ : Tree P → Con CP)
    → Forest P × Forest P
    → Stable {CP = CP} (Flow (QuanticNucleus.GC N))
  stableCut N φ ψ (pf , rf) =
    let
      module QN = Nucleus.QuanticNucleusLocal N
    in
    QN.stable-· (stableForest N φ pf) (stableForest N ψ rf)

  stableJoinCuts
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ ψ : Tree P → Con CP)
    → Stable {CP = CP} (Flow (QuanticNucleus.GC N))
    → List (Forest P × Forest P)
    → Stable {CP = CP} (Flow (QuanticNucleus.GC N))
  stableJoinCuts N φ ψ acc [] = acc
  stableJoinCuts N φ ψ acc (c ∷ cs) =
    let
      module QN = Nucleus.QuanticNucleusLocal N
    in
    stableJoinCuts N φ ψ (QN.stable-⊔ᶠ acc (stableCut N φ ψ c)) cs

  StableChar
    : QuanticNucleus {CP = CP} JP
    → Set (ℓP ⊔ lsuc (ℓCon ⊔ ℓRel))
  StableChar N = Tree P → Stable {CP = CP} (Flow (QuanticNucleus.GC N))

  renormalisedCharStable
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ : Tree P → Con CP)
    → StableChar N
  renormalisedCharStable N φ t =
    mkStable
      (renormalise N (φ t))
      (GuardedClosure.idemp-lax (QuanticNucleus.GC N) (φ t))

  stableConvolution
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ ψ : Tree P → Con CP)
    → StableChar N
  stableConvolution N φ ψ t =
    stableJoinCuts N φ ψ (stableCut N φ ψ (cutHead t)) (cutTail t)

  renormalisedConvolution
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ ψ : Tree P → Con CP)
    → Tree P → Con CP
  renormalisedConvolution N φ ψ t =
    elem (stableConvolution N φ ψ t)

  renormalisedConvolution-least
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ ψ : Tree P → Con CP)
    → (χ : StableChar N)
    → ∀ t
    → _⊑_ CP ((φ ⋆ ψ) t) (elem (χ t))
    → _⊑_ CP (renormalisedConvolution N φ ψ t) (elem (χ t))
  renormalisedConvolution-least N φ ψ χ t convolution≤χ =
    stableJoinCutsLeast
      (stableCut N φ ψ (cutHead t))
      (stableCut≤χ here)
      (cutTail t)
      (λ {y} y∈cuts → stableCut≤χ (there y∈cuts))
    where
      module QN = Nucleus.QuanticNucleusLocal N

      rawCutValue : Forest P × Forest P → Con CP
      rawCutValue (pf , rf) =
        forestEval φ pf · forestEval ψ rf

      stableCut≤χ
        : ∀ {c}
        → c ∈ (cutHead t ∷ cutTail t)
        → _⊑_ CP (elem (stableCut N φ ψ c)) (elem (χ t))
      stableCut≤χ {c = (pf , rf)} c∈cuts =
        let
          c = (pf , rf)
          raw≤convolution
            : _⊑_ CP (rawCutValue c) ((φ ⋆ ψ) t)
          raw≤convolution =
            joinList-ub (map-∈ rawCutValue c∈cuts)

          raw≤χ
            : _⊑_ CP (rawCutValue c) (elem (χ t))
          raw≤χ =
            begin⊑
              rawCutValue c ⊑⟨ raw≤convolution ⟩
              (φ ⋆ ψ) t ⊑⟨ convolution≤χ ⟩
              elem (χ t) ∎⊑

          flowProduct≤χ
            : _⊑_ CP
                (elem (stableForest N φ pf) · elem (stableForest N ψ rf))
                (elem (χ t))
          flowProduct≤χ =
            begin⊑
              (elem (stableForest N φ pf) · elem (stableForest N ψ rf))
                ⊑⟨ QuanticNucleus.lax-· N (forestEval φ pf) (forestEval ψ rf) ⟩
              Flow (QuanticNucleus.GC N) (rawCutValue c)
                ⊑⟨ QN.stable-over-approx-least (χ t) raw≤χ ⟩
              elem (χ t) ∎⊑
        in
        QN.stable-over-approx-least (χ t) flowProduct≤χ

      stableJoinCutsLeast
        : (acc : Stable {CP = CP} (Flow (QuanticNucleus.GC N)))
        → _⊑_ CP (elem acc) (elem (χ t))
        → (cs : List (Forest P × Forest P))
        → (∀ {c} → c ∈ cs → _⊑_ CP (elem (stableCut N φ ψ c)) (elem (χ t)))
        → _⊑_ CP (elem (stableJoinCuts N φ ψ acc cs)) (elem (χ t))
      stableJoinCutsLeast acc acc≤χ [] _ =
        acc≤χ
      stableJoinCutsLeast acc acc≤χ (c ∷ cs) cs≤χ =
        stableJoinCutsLeast
          (QN.stable-⊔ᶠ acc (stableCut N φ ψ c))
          (⊔ᶠ-least acc≤χ (cs≤χ here))
          cs
          (λ {d} d∈cs → cs≤χ (there d∈cs))

  stableConvolution-least
    : (N : QuanticNucleus {CP = CP} JP)
    → (φ ψ : Tree P → Con CP)
    → (χ : StableChar N)
    → ∀ t
    → _⊑_ CP ((φ ⋆ ψ) t) (elem (χ t))
    → _⊑_ CP (elem (stableConvolution N φ ψ t)) (elem (χ t))
  stableConvolution-least = renormalisedConvolution-least

  record StableConvolutionTheorem
    (N : QuanticNucleus {CP = CP} JP)
    : Set (lsuc (ℓCon ⊔ ℓRel ⊔ ℓP))
    where
    field
      theorem-stableConvolution
        : (φ ψ : Tree P → Con CP)
        → StableChar N

      theorem-stableConvolution-least
        : (φ ψ : Tree P → Con CP)
        → (χ : StableChar N)
        → ∀ t
        → _⊑_ CP ((φ ⋆ ψ) t) (elem (χ t))
        → _⊑_ CP (elem (theorem-stableConvolution φ ψ t)) (elem (χ t))

      theorem-renormalisedCharStable
        : (φ : Tree P → Con CP)
        → StableChar N

      theorem-renormalisedConvolution
        : (φ ψ : Tree P → Con CP)
        → Tree P → Con CP

      theorem-renormalisedConvolution-least
        : (φ ψ : Tree P → Con CP)
        → (χ : StableChar N)
        → ∀ t
        → _⊑_ CP ((φ ⋆ ψ) t) (elem (χ t))
        → _⊑_ CP (theorem-renormalisedConvolution φ ψ t) (elem (χ t))

  stableConvolutionTheorem
    : (N : QuanticNucleus {CP = CP} JP)
    → StableConvolutionTheorem N
  stableConvolutionTheorem N =
    record
      { theorem-stableConvolution = stableConvolution N
      ; theorem-stableConvolution-least = stableConvolution-least N
      ; theorem-renormalisedCharStable = renormalisedCharStable N
      ; theorem-renormalisedConvolution = renormalisedConvolution N
      ; theorem-renormalisedConvolution-least = renormalisedConvolution-least N
      }
