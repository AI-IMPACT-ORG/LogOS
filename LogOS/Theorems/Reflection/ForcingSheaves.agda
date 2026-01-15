{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Reflection.ForcingSheaves where

open import LogOS.Prelude
open import Data.List using (List; []; _∷_; _++_; concat)
open import LogOS.Minimal.Con using (ConPoset; PredConPoset)
open import LogOS.Minimal.Closure using (ClosureOp)
import LogOS.Syntax.Prop as Prop
open import LogOS.Syntax.Prop using (_↔_; intro)

-- Minimal list-wise predicate.
data All {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁}
         (P : A → Set ℓ₂) : List A → Set (ℓ₁ ⊔ ℓ₂) where
  all[] : All P []
  all∷  : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

All-map
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁}
    {P : A → Set ℓ₂} {Q : A → Set ℓ₃}
  → (∀ x → P x → Q x)
  → ∀ {xs} → All P xs → All Q xs
All-map f all[] = all[]
All-map f (all∷ px pxs) = all∷ (f _ px) (All-map f pxs)

All-++ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
       → ∀ {xs ys} → All P xs → All P ys → All P (xs ++ ys)
All-++ all[] ys = ys
All-++ (all∷ px pxs) ys = all∷ px (All-++ pxs ys)

All-concat
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → ∀ {xss} → All (All P) xss → All P (concat xss)
All-concat all[] = all[]
All-concat (all∷ px pxs) = All-++ px (All-concat pxs)

-- Extract the list-of-lists payload from an All of dependent pairs.
listsOf
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
    {R : A → List A → Set ℓ₂}
    {cs : List A}
  → All (λ c → Σ (List A) (λ ds → R c ds)) cs
  → List (List A)
listsOf all[] = []
listsOf (all∷ (ds , _) rest) = ds ∷ listsOf rest

-- Coverage on a preorder (poset-site, list-based).
record Coverage {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    Cover : Con → List Con → Set ℓ
    id-cover : ∀ p → Cover p (p ∷ [])
    trans-cover
      : ∀ {p cs}
      → Cover p cs
      → (covs : All (λ c → Σ (List Con) (λ ds → Cover c ds)) cs)
      → Cover p (concat (listsOf covs))

-- Avoid opening Coverage globally: its fields are also projections and this can
-- lead to ambiguous projection resolution under `-W all -W error`.

module _ {ℓ : Level} {CP : ConPoset ℓ} (Cov : Coverage CP) where
  open ConPoset CP
  open Coverage Cov

  PredCP : ConPoset (lsuc ℓ)
  PredCP = PredConPoset Con

  localOp : (Con → Set ℓ) → Con → Set ℓ
  localOp U p = Σ (List Con) (λ cs → Cover p cs × All U cs)

  idempLocal
    : ∀ U → ConPoset._⊑_ PredCP (localOp (localOp U)) (localOp U)
  idempLocal U = lift idempLocal'
    where
      idempLocal' : ∀ p → localOp (localOp U) p → localOp U p
      idempLocal' p (cs , (cov , allLoc)) =
        concat (listsOf (coversOf allLoc)) , (cover' , allU')
        where
          coversOf
            : ∀ {cs}
            → All (λ c → Σ (List Con) (λ ds → Cover c ds × All U ds)) cs
            → All (λ c → Σ (List Con) (λ ds → Cover c ds)) cs
          coversOf all[] = all[]
          coversOf (all∷ (ds , (cov' , _)) rest) =
            all∷ (ds , cov') (coversOf rest)

          allUOf
            : ∀ {cs}
            → (locs : All (λ c → Σ (List Con) (λ ds → Cover c ds × All U ds)) cs)
            → All (All U) (listsOf (coversOf locs))
          allUOf all[] = all[]
          allUOf (all∷ (ds , (_ , allU)) rest) =
            all∷ allU (allUOf rest)

          cover' = trans-cover cov (coversOf allLoc)
          allU' = All-concat (allUOf allLoc)

  localClosure : ClosureOp PredCP
  localClosure =
    record
      { cl = localOp
      ; mono = λ {U} {V} U≤V →
          lift (λ p (cs , (cov , allU)) →
            cs , (cov , All-map (λ c u → Lift.lower U≤V c u) allU))
      ; infl = λ U → lift (λ p u → (p ∷ []) , (id-cover p , all∷ u all[]))
      ; idemp-lax = idempLocal
      }

  -- Sheaves are exactly the fixed points of the local operator.
  Sheaf : (Con → Set ℓ) → Set ℓ
  Sheaf U = ∀ p cs → Cover p cs → All U cs → U p

  sheaf→fixed : ∀ {U} → Sheaf U → ConPoset._⊑_ PredCP (localOp U) U
  sheaf→fixed sh = lift (λ p (cs , (cov , allU)) → sh p cs cov allU)

  fixed→sheaf : ∀ {U} → ConPoset._⊑_ PredCP (localOp U) U → Sheaf U
  fixed→sheaf fixed p cs cov allU =
    Lift.lower fixed p (cs , (cov , allU))

  sheaf↔fixed : ∀ {U} → Sheaf U ↔ ConPoset._⊑_ PredCP (localOp U) U
  sheaf↔fixed = intro sheaf→fixed fixed→sheaf

-- Coverage equivalence: two presentations of the same site induce the same
-- sheaf semantics (forcing is invariant under observationally equivalent covers).

module CoverageEq {ℓ : Level} {CP : ConPoset ℓ}
                  (Cov₁ Cov₂ : Coverage CP) where
  open Coverage Cov₁ renaming (Cover to Cover₁)
  open Coverage Cov₂ renaming (Cover to Cover₂)
  open ConPoset CP

  localOp₁ : (Con → Set ℓ) → Con → Set ℓ
  localOp₁ U p = Σ (List Con) (λ cs → Cover₁ p cs × All U cs)

  localOp₂ : (Con → Set ℓ) → Con → Set ℓ
  localOp₂ U p = Σ (List Con) (λ cs → Cover₂ p cs × All U cs)

  Sheaf₁ : (Con → Set ℓ) → Set ℓ
  Sheaf₁ U = ∀ p cs → Cover₁ p cs → All U cs → U p

  Sheaf₂ : (Con → Set ℓ) → Set ℓ
  Sheaf₂ U = ∀ p cs → Cover₂ p cs → All U cs → U p

  Cover≈ : Set ℓ
  Cover≈ = ∀ p cs → Cover₁ p cs ↔ Cover₂ p cs

  localOp-≈ : Cover≈ → ∀ {U} {p} → localOp₁ U p ↔ localOp₂ U p
  localOp-≈ cov≈ {U} {p} =
    intro
      (λ (cs , (cov , allU)) →
        cs , (Prop._↔_.to (cov≈ p cs) cov , allU))
      (λ (cs , (cov , allU)) →
        cs , (Prop._↔_.from (cov≈ p cs) cov , allU))

  sheaf-≈ : Cover≈ → ∀ {U} → Sheaf₁ U ↔ Sheaf₂ U
  sheaf-≈ cov≈ =
    intro
      (λ sh p cs cov allU → sh p cs (Prop._↔_.from (cov≈ p cs) cov) allU)
      (λ sh p cs cov allU → sh p cs (Prop._↔_.to (cov≈ p cs) cov) allU)
