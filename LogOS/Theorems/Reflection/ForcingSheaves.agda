{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Reflection.ForcingSheaves where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_; _++_; concat; All; all[]; all∷; All-map; All-++; All-concat; listsOf)
open import LogOS.Minimal.Con using (ConPreorder; PredConPreorder)
open import LogOS.Minimal.Closure using (ClosureOp)
import LogOS.Syntax.Prop as Prop
open import LogOS.Syntax.Prop using (_↔_; intro)

-- Coverage on a preorder (poset-site when antisymmetry is supplied; list-based).
record Coverage {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
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

module _ {ℓ : Level} {CP : ConPreorder ℓ} (Cov : Coverage CP) where
  open ConPreorder CP
  open Coverage Cov

  PredCP : ConPreorder (lsuc ℓ)
  PredCP = PredConPreorder Con

  localOp : (Con → Set ℓ) → Con → Set ℓ
  localOp U p = Σ (List Con) (λ cs → Cover p cs × All U cs)

  idempLocal
    : ∀ U → ConPreorder._⊑_ PredCP (localOp (localOp U)) (localOp U)
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

  sheaf→fixed : ∀ {U} → Sheaf U → ConPreorder._⊑_ PredCP (localOp U) U
  sheaf→fixed sh = lift (λ p (cs , (cov , allU)) → sh p cs cov allU)

  fixed→sheaf : ∀ {U} → ConPreorder._⊑_ PredCP (localOp U) U → Sheaf U
  fixed→sheaf fixed p cs cov allU =
    Lift.lower fixed p (cs , (cov , allU))

  sheaf↔fixed : ∀ {U} → Sheaf U ↔ ConPreorder._⊑_ PredCP (localOp U) U
  sheaf↔fixed = intro sheaf→fixed fixed→sheaf

-- Coverage equivalence: two presentations of the same site induce the same
-- sheaf semantics (forcing is invariant under observationally equivalent covers).

module CoverageEq {ℓ : Level} {CP : ConPreorder ℓ}
                  (Cov₁ Cov₂ : Coverage CP) where
  open Coverage Cov₁ renaming (Cover to Cover₁)
  open Coverage Cov₂ renaming (Cover to Cover₂)
  open ConPreorder CP

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
