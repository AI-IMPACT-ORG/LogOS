{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Truth where

open import LogOS.Prelude
open import Data.Product using (_×_; _,_; fst; snd)
open import LogOS.Base.Signature
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adapter

-- Minimal S/H/G truth interfaces with explicit laxness

module StrictTruth {ℓ : Level} (Sig : LogOSSignature ℓ) where
  open LogOSSignature Sig
  -- Strict layer interface, supplied by models when needed
  record StrictLayer (Fml : Set ℓ) : Set (lsuc ℓ) where
    infix 2 _⊢S_
    field
      Sat_S : Cosp → Fml → Set ℓ
      _⊢S_  : Set ℓ → Set ℓ → Set ℓ

module HomotypicalTruth {ℓ : Level}
                        (Sig : LogOSSignature ℓ)
                        (Q   : QAdapter ℓ)
                        (WH  : Worlds.WorldH Sig Q)
                        where
  open LogOSSignature Sig
  open Worlds Sig
  open QAdapter Q
  open Worlds.WorldH WH using (_≤ctx_)
  -- Constraints and satisfaction in H-tier
  record HLayer (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
    open BulkBoundary BB
    field
      Sat_H : Cosp → Con_bnd → Set ℓ
      -- Monotonicities (Kripke + constraint)
      mono-Con  : ∀ {w c c'} → _⊑bnd_ c c' → Sat_H w c → Sat_H w c'
      mono-ctx  : ∀ {w w' c} → _≤ctx_ w w' → Sat_H w c → Sat_H w' c

  -- Invariance closure (lax)
  record Invariance (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
    open BulkBoundary BB
    field
      -- Axiom: invariance closure on constraints
      Inv_H        : Con_bnd → Con_bnd
      -- Axiom: inflationary c ≤ Inv_H c
      infl         : ∀ c → _⊑bnd_ c (Inv_H c)
      -- Axiom: idempotent up to ⊑ Inv_H (Inv_H c) ≤ Inv_H c
      idemp-lax    : ∀ c → _⊑bnd_ (Inv_H (Inv_H c)) (Inv_H c)

  -- Bulk/boundary lax adjunction
  open import LogOS.Minimal.Adjunction using (LaxAdjunction; LaxMonoidalAdjunction)

module GuardedCore {ℓ : Level} where

  -- Guarded closure with a (lax) fixed point Th*
  record GuardedClosure (CP : ConPoset ℓ) : Set (lsuc ℓ) where
    open ConPoset CP
    field
      -- Axiom: global flow step
      Flow        : Con → Con
      -- Axiom: monotone; inflationary; idempotent up to ⊑
      mono        : ∀ {c c'} → _⊑_ c c' → _⊑_ (Flow c) (Flow c')
      infl        : ∀ c → _⊑_ c (Flow c)
      idemp-lax   : ∀ c → _⊑_ (Flow (Flow c)) (Flow c)
      -- Axiom: least fixed point characterisation via inequalities
      Th*         : Con
      Th*-fixed   : (_⊑_ (Th*) (Flow Th*)) × (_⊑_ (Flow Th*) Th*)
      -- Approximants Th₀, Th₁, … and dcpo structure can be provided by models

  -- Flow homomorphism (lax): map ∘ F₁ ⊑ F₂ ∘ map and map Th*₁ ⊑ Th*₂
  record FlowHom (CP₁ CP₂ : ConPoset ℓ)
                 (G₁ : GuardedClosure CP₁)
                 (G₂ : GuardedClosure CP₂)
                 (map : ConPoset.Con CP₁ → ConPoset.Con CP₂)
                 : Set (lsuc ℓ) where
    open ConPoset CP₂ using (_⊑_)
    open GuardedClosure G₁ renaming (Flow to F₁; Th* to Th₁)
    open GuardedClosure G₂ renaming (Flow to F₂; Th* to Th₂)
    field
      preserves-F  : ∀ c → _⊑_ (map (F₁ c)) (F₂ (map c))
      preserves-Th : _⊑_ (map Th₁) Th₂

  -- Graded guarded closure: grade-indexed flow + saturation grade for fixed points.
  record GradedClosure (Q : QAdapter ℓ)
                       (CP : ConPoset ℓ)
                       : Set (lsuc ℓ) where
    open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_; _·_ to _∙_; e to ε)
    open ConPoset CP
    field
      Flow       : Grade → Con → Con
      mono       : ∀ {g c c'} → _⊑_ c c' → _⊑_ (Flow g c) (Flow g c')
      mono-grade : ∀ {g g'} → _≤g_ g g' → ∀ c → _⊑_ (Flow g c) (Flow g' c)
      -- Grade order convention: `comp-lax` witnesses one-step composition as
      -- `Flow g' (Flow g c) ⊑ Flow (g ∙ g') c`.
      comp-lax   : ∀ g g' c → _⊑_ (Flow g' (Flow g c)) (Flow (g ∙ g') c)

      sat        : Grade
      sat-top    : ∀ g → _≤g_ g sat
      infl-sat   : ∀ c → _⊑_ c (Flow sat c)
      idemp-sat  : ∀ c → _⊑_ (Flow sat (Flow sat c)) (Flow sat c)
      Th*        : Con
      Th*-fixed  : (_⊑_ Th* (Flow sat Th*)) × (_⊑_ (Flow sat Th*) Th*)

  -- Lax grade morphism (monotone, monoid-compatible).
  record GradeHom (Q₁ Q₂ : QAdapter ℓ) : Set (lsuc ℓ) where
    module Q1 = QAdapter Q₁
    module Q2 = QAdapter Q₂
    field
      map      : Q1.Scale → Q2.Scale
      mono     : ∀ {g g'} → Q1._≤s_ g g' → Q2._≤s_ (map g) (map g')
      unit-lax : Q2._≤s_ Q2.e (map Q1.e)
      mul-lax  : ∀ g g' → Q2._≤s_ (Q2._·_ (map g) (map g')) (map (Q1._·_ g g'))

  -- Graded flow homomorphism (same grade carrier).
  record GradedFlowHom {Q : QAdapter ℓ}
                       (CP₁ CP₂ : ConPoset ℓ)
                       (G₁ : GradedClosure Q CP₁)
                       (G₂ : GradedClosure Q CP₂)
                       (map : ConPoset.Con CP₁ → ConPoset.Con CP₂)
                       : Set (lsuc ℓ) where
    open ConPoset CP₂ using (_⊑_)
    open GradedClosure G₁ renaming (Flow to F₁; Th* to Th₁)
    open GradedClosure G₂ renaming (Flow to F₂; Th* to Th₂)
    field
      preserves-F  : ∀ g c → _⊑_ (map (F₁ g c)) (F₂ g (map c))
      preserves-Th : _⊑_ (map Th₁) Th₂

  -- Graded flow homomorphism with a grade morphism.
  record GradedFlowHomWithGrade {Q₁ Q₂ : QAdapter ℓ}
                                (CP₁ CP₂ : ConPoset ℓ)
                                (G₁ : GradedClosure Q₁ CP₁)
                                (G₂ : GradedClosure Q₂ CP₂)
                                (φ : GradeHom Q₁ Q₂)
                                (map : ConPoset.Con CP₁ → ConPoset.Con CP₂)
                                : Set (lsuc ℓ) where
    open ConPoset CP₂ using (_⊑_)
    open GradedClosure G₁ renaming (Flow to F₁; Th* to Th₁; sat to sat₁)
    open GradedClosure G₂ renaming (Flow to F₂; Th* to Th₂; sat to sat₂)
    open GradeHom φ renaming (map to grade-map)
    field
      preserves-F  : ∀ g c → _⊑_ (map (F₁ g c)) (F₂ (grade-map g) (map c))
      preserves-Th : _⊑_ (map Th₁) Th₂
      sat≤         : QAdapter._≤s_ Q₂ (grade-map sat₁) sat₂

  -- Forget grading by taking the saturation grade.
  forgetGradedClosure
    : ∀ {Q : QAdapter ℓ} {CP : ConPoset ℓ}
    → GradedClosure Q CP
    → GuardedClosure CP
  forgetGradedClosure {Q = Q} {CP = CP} GC =
    record
      { Flow      = Flow sat
      ; mono      = λ {c} {c'} le → mono {g = sat} le
      ; infl      = infl-sat
      ; idemp-lax = idemp-sat
      ; Th*       = Th*
      ; Th*-fixed = Th*-fixed
      }
    where
      open GradedClosure GC

  -- Optional ω-CPO structure (finite-first via ω-approximants, Scott continuity)
  record OmegaCPO (CP : ConPoset ℓ) : Set (lsuc ℓ) where
    open ConPoset CP
    field
      ⊥      : Con
      isBot  : ∀ c → _⊑_ ⊥ c
      supω   : (ℕ → Con) → Con
      ub     : ∀ (f : ℕ → Con) (n : ℕ) → _⊑_ (f n) (supω f)
      least  : ∀ (f : ℕ → Con) (x : Con) → (∀ n → _⊑_ (f n) x) → _⊑_ (supω f) x

  -- Optional continuity and finite-first specification, layered over GuardedClosure
  record FiniteFirst (CP : ConPoset ℓ)
                      (GC : GuardedClosure CP)
                      (ωCPO : OmegaCPO CP)
                      : Set (lsuc ℓ) where
    open ConPoset CP
    open GuardedClosure GC renaming (Flow to F; Th* to Th⋆)
    open OmegaCPO ωCPO
    field
      approx0  : Con
      approxS  : (ℕ → Con)
      base     : approxS zero ≡ ⊥
      step     : ∀ n → approxS (suc n) ≡ F (approxS n)
      Th⋆-as-sup : (_⊑_ Th⋆ (supω approxS)) × (_⊑_ (supω approxS) Th⋆)
      -- Scott continuity (lax) w.r.t. ω-chains
      cont-ω : ∀ (f : ℕ → Con)
                (mono-chain : ∀ n → _⊑_ (f n) (f (suc n))) →
                _⊑_ (F (supω f)) (supω (λ n → F (f n)))

  -- Induction principle (lax μ-induction) under FiniteFirst
  μ-induction
    : ∀ {CP : ConPoset ℓ}
      (GC : GuardedClosure CP)
      (ωCPO : OmegaCPO CP)
      (FF : FiniteFirst CP GC ωCPO)
      (c : ConPoset.Con CP)
      → ConPoset._⊑_ CP (GuardedClosure.Flow GC c) c
      → ConPoset._⊑_ CP (GuardedClosure.Th* GC) c
  μ-induction {CP} GC ωCPO FF c pre =
    ConPoset.trans CP p sup≤c
    where
      open ConPoset CP
      open GuardedClosure GC renaming (Flow to F; Th* to Th⋆)
      open OmegaCPO ωCPO
      open FiniteFirst FF renaming (approxS to A; base to baseEq; step to stepEq; Th⋆-as-sup to supineq)
      -- Show each approximant ≤ c by induction on n
      chain : (n : ℕ) → _⊑_ (A n) c
      chain zero = subst (λ x → _⊑_ x c) (sym baseEq) (isBot c)
      chain (suc n) =
        subst (λ x → _⊑_ x c)
              (sym (stepEq n))
              (ConPoset.trans CP (GuardedClosure.mono GC (chain n)) pre)
      sup≤c = least A c (λ n → chain n)
      pq : (_⊑_ Th⋆ (supω A)) × (_⊑_ (supω A) Th⋆)
      pq = supineq
      p : _⊑_ Th⋆ (supω A)
      p = fst pq
      q : _⊑_ (supω A) Th⋆
      q = snd pq

module GuardedTruth {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  open LogOSSignature Sig
  open Worlds Sig
  open GuardedCore {ℓ} public
