{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Truth where

open import LogOS.Prelude
open import Data.Product using (_×_; _,_; fst; snd)
open import LogOS.Base.Signature
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure
open import LogOS.Minimal.Adapter

-- Minimal S/H/G truth interfaces with explicit laxness

module StrictTruth {ℓ : Level} (Sig : LogOSSignature ℓ) where
  open LogOSSignature Sig
  -- Strict layer interface, supplied by models when needed
  record StrictLayer (Fml : Set ℓ) : Set (lsuc ℓ) where
    field
      Sat_S : Cosp → Fml → Set ℓ

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
      -- Axiom: chosen (lax) fixed point witness via inequalities.
      -- Leastness / induction principles are derived separately once additional
      -- domain structure (e.g. ωCPO + finite-first approximants) is provided.
      Th*         : Con
      Th*-fixed   : (_⊑_ (Th*) (Flow Th*)) × (_⊑_ (Flow Th*) Th*)
      -- Approximants Th₀, Th₁, … and dcpo structure can be provided by models

  -- Forget the distinguished fixed point: a guarded closure always yields a
  -- plain closure operator.
  closureOfGuardedClosure
    : ∀ {CP : ConPoset ℓ}
    → GuardedClosure CP → ClosureOp CP
  closureOfGuardedClosure G =
    record
      { cl        = GuardedClosure.Flow G
      ; mono      = GuardedClosure.mono G
      ; infl      = GuardedClosure.infl G
      ; idemp-lax = GuardedClosure.idemp-lax G
      }

  -- Flow homomorphism (lax): map ∘ F₁ ⊑ F₂ ∘ map and map Th*₁ ⊑ Th*₂.
  --
  -- Note: monotonicity of `map` itself (w.r.t. `_⊑_`) is intentionally not part
  -- of this record; it is usually supplied by the surrounding structure (e.g.
  -- kernel/constraint algebra homs provide a `MonoMap` separately).
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

  -- Saturation grade induces a (plain) closure operator.
  closureOfGradedClosure-sat
    : ∀ {Q : QAdapter ℓ} {CP : ConPoset ℓ}
    → GradedClosure Q CP → ClosureOp CP
  closureOfGradedClosure-sat GC =
    record
      { cl        = GradedClosure.Flow GC (GradedClosure.sat GC)
      ; mono      = λ {c} {c'} le → GradedClosure.mono GC le
      ; infl      = GradedClosure.infl-sat GC
      ; idemp-lax = GradedClosure.idemp-sat GC
      }

  -- Lax grade morphism (monotone, monoid-compatible).
  record GradeHom (Q₁ Q₂ : QAdapter ℓ) : Set (lsuc ℓ) where
    module Q1 = QAdapter Q₁
    module Q2 = QAdapter Q₂
    field
      map      : Q1.Scale → Q2.Scale
      mono     : ∀ {g g'} → Q1._≤s_ g g' → Q2._≤s_ (map g) (map g')
      unit-lax : Q2._≤s_ Q2.e (map Q1.e)
      mul-lax  : ∀ g g' → Q2._≤s_ (Q2._·_ (map g) (map g')) (map (Q1._·_ g g'))
      -- Lax finite-join preservation (quantale “additive” structure).
      --
      -- The inequality direction is chosen to match the library’s “upper envelope”
      -- reading of joins: mapping a combined budget should be at least as large
      -- as combining mapped budgets.
      join-lax : ∀ g g' → Q2._≤s_ (Q2._⊔s_ (map g) (map g')) (map (Q1._⊔s_ g g'))
      bot-lax  : Q2._≤s_ Q2.⊥s (map Q1.⊥s)

  -- Small builder: extend a monoid-lax grade map to a lax quantale hom by
  -- deriving the join/bottom laws from monotonicity + finite joins.
  mkGradeHom
    : ∀ {Q₁ Q₂ : QAdapter ℓ}
      (map : QAdapter.Scale Q₁ → QAdapter.Scale Q₂)
      (mono : ∀ {g g'} → QAdapter._≤s_ Q₁ g g' → QAdapter._≤s_ Q₂ (map g) (map g'))
      (unit-lax : QAdapter._≤s_ Q₂ (QAdapter.e Q₂) (map (QAdapter.e Q₁)))
      (mul-lax  : ∀ g g' →
                  QAdapter._≤s_ Q₂
                    (QAdapter._·_ Q₂ (map g) (map g'))
                    (map (QAdapter._·_ Q₁ g g')))
      → GradeHom Q₁ Q₂
  mkGradeHom {Q₁ = Q₁} {Q₂ = Q₂} map mono unit-lax mul-lax =
    record
      { map = map
      ; mono = mono
      ; unit-lax = unit-lax
      ; mul-lax = mul-lax
      ; join-lax = joinLax
      ; bot-lax  = QAdapter.⊥s-least Q₂ (map (QAdapter.⊥s Q₁))
      }
    where
      joinLax
        : ∀ g g'
          → QAdapter._≤s_ Q₂
              (QAdapter._⊔s_ Q₂ (map g) (map g'))
              (map (QAdapter._⊔s_ Q₁ g g'))
      joinLax g g' =
        QAdapter.⊔s-least Q₂
          (mono (QAdapter.⊔s-ub₁ Q₁ g g'))
          (mono (QAdapter.⊔s-ub₂ Q₁ g g'))

  -- Identity and composition for grade morphisms.
  --
  -- These live in the minimal core so higher layers (kernel morphisms, bridges)
  -- can compose grade maps without re-proving quantale/monoid coherence.

  idGradeHom : ∀ {Q : QAdapter ℓ} → GradeHom Q Q
  idGradeHom {Q} =
    mkGradeHom (λ g → g) (λ le → le)
      (QAdapter.≤s-refl Q)
      (λ _ _ → QAdapter.≤s-refl Q)

  composeGradeHom
    : ∀ {Q₁ Q₂ Q₃ : QAdapter ℓ}
      → GradeHom Q₁ Q₂
      → GradeHom Q₂ Q₃
      → GradeHom Q₁ Q₃
  composeGradeHom {Q₁ = Q₁} {Q₂ = Q₂} {Q₃ = Q₃} φ ψ =
    record
      { map      = mapComp
      ; mono     = monoComp
      ; unit-lax = unitComp
      ; mul-lax  = mulComp
      ; join-lax = joinComp
      ; bot-lax  = botComp
      }
    where
      open GradeHom φ renaming
        ( map      to map₁
        ; mono     to mono₁
        ; unit-lax to unit₁
        ; mul-lax  to mul₁
        ; join-lax to join₁
        ; bot-lax  to bot₁
        )
      open GradeHom ψ renaming
        ( map      to map₂
        ; mono     to mono₂
        ; unit-lax to unit₂
        ; mul-lax  to mul₂
        ; join-lax to join₂
        ; bot-lax  to bot₂
        )

      mapComp : QAdapter.Scale Q₁ → QAdapter.Scale Q₃
      mapComp g = map₂ (map₁ g)

      monoComp : ∀ {g g'} → QAdapter._≤s_ Q₁ g g' → QAdapter._≤s_ Q₃ (mapComp g) (mapComp g')
      monoComp le = mono₂ (mono₁ le)

      unitComp : QAdapter._≤s_ Q₃ (QAdapter.e Q₃) (mapComp (QAdapter.e Q₁))
      unitComp =
        QAdapter.≤s-trans Q₃
          unit₂
          (mono₂ unit₁)

      mulComp
        : ∀ g g'
          → QAdapter._≤s_ Q₃
              (QAdapter._·_ Q₃ (mapComp g) (mapComp g'))
              (mapComp (QAdapter._·_ Q₁ g g'))
      mulComp g g' =
        QAdapter.≤s-trans Q₃
          (mul₂ (map₁ g) (map₁ g'))
          (mono₂ (mul₁ g g'))

      joinComp
        : ∀ g g'
          → QAdapter._≤s_ Q₃
              (QAdapter._⊔s_ Q₃ (mapComp g) (mapComp g'))
              (mapComp (QAdapter._⊔s_ Q₁ g g'))
      joinComp g g' =
        QAdapter.≤s-trans Q₃
          (join₂ (map₁ g) (map₁ g'))
          (mono₂ (join₁ g g'))

      botComp : QAdapter._≤s_ Q₃ (QAdapter.⊥s Q₃) (mapComp (QAdapter.⊥s Q₁))
      botComp =
        QAdapter.≤s-trans Q₃
          bot₂
          (mono₂ bot₁)

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
      ; mono      = λ {c} {c'} le → GradedClosure.mono GC {g = sat} le
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

  -- Generic Kleene μ-calculus on a boundary preorder:
  -- define μ as the ω-sup of approximants from ⊥, and derive Park/least-pre-fixed
  -- point induction. This is independent of any distinguished `Th*`.

  module Kleene
    {CP : ConPoset ℓ}
    (ωCPO : OmegaCPO CP)
    where
    open ConPoset CP
    open OmegaCPO ωCPO

    -- Iteration from ⊥ (Kleene approximants).
    iter : (Con → Con) → ℕ → Con
    iter F zero    = ⊥
    iter F (suc n) = F (iter F n)

    μ : (Con → Con) → Con
    μ F = supω (iter F)

    -- “Unfold-left”: μF is always below one more step (no continuity needed).
    μ-unfold-left
      : (F : Con → Con)
      → MonoOn CP F
      → _⊑_ (μ F) (F (μ F))
    μ-unfold-left F monoF =
      least (iter F) (F (μ F)) ubF
      where
        ubF : ∀ n → _⊑_ (iter F n) (F (μ F))
        ubF zero = isBot (F (μ F))
        ubF (suc n) = monoF (ub (iter F) n)

    -- Park/least-pre-fixed-point induction for μF.
    μ-induction
      : (F : Con → Con)
      → MonoOn CP F
      → ∀ c → _⊑_ (F c) c → _⊑_ (μ F) c
    μ-induction F monoF c pre =
      least (iter F) c (iter≤c pre)
      where
        iter≤c : _⊑_ (F c) c → ∀ n → _⊑_ (iter F n) c
        iter≤c _ zero = isBot c
        iter≤c pre (suc n) =
          ConPoset.trans CP (monoF (iter≤c pre n)) pre

    -- Scott-continuity (lax) for an endomap on an ωCPO preorder.
    record ScottContinuous (F : Con → Con) : Set (lsuc ℓ) where
      field
        cont-ω : ∀ (f : ℕ → Con)
                 (mono-chain : ∀ n → _⊑_ (f n) (f (suc n)))
               → _⊑_ (F (supω f)) (supω (λ n → F (f n)))

    -- Tail-sup is always bounded by the full sup: sup (f ∘ suc) ⊑ sup f.
    supω-tail≤
      : (f : ℕ → Con)
      → _⊑_ (supω (λ n → f (suc n))) (supω f)
    supω-tail≤ f =
      least (λ n → f (suc n)) (supω f) (λ n → ub f (suc n))

    -- Any inflationary endomap yields an increasing Kleene chain.
    iter-mono-chain-infl
      : (F : Con → Con)
      → (inflF : ∀ c → _⊑_ c (F c))
      → ∀ n → _⊑_ (iter F n) (iter F (suc n))
    iter-mono-chain-infl F inflF zero =
      isBot (F ⊥)
    iter-mono-chain-infl F inflF (suc n) =
      inflF (iter F (suc n))

    -- “Unfold-right”: under Scott continuity (and any chosen chain witness),
    -- μF is also a pre-fixed point: F (μF) ⊑ μF.
    μ-unfold-right
      : (F : Con → Con)
      → ScottContinuous F
      → (mono-chain : ∀ n → _⊑_ (iter F n) (iter F (suc n)))
      → _⊑_ (F (μ F)) (μ F)
    μ-unfold-right F SC mono-chain =
      ConPoset.trans CP step₁ step₂
      where
        open ScottContinuous SC
        step₁ : _⊑_ (F (μ F)) (supω (λ n → F (iter F n)))
        step₁ = cont-ω (iter F) mono-chain

        step₂ : _⊑_ (supω (λ n → F (iter F n))) (μ F)
        step₂ =
          -- F (iter n) is definitionally iter (suc n)
          supω-tail≤ (iter F)

    -- Turnkey version: derive the chain witness from inflationarity.
    μ-unfold-right-infl
      : (F : Con → Con)
      → ScottContinuous F
      → (inflF : ∀ c → _⊑_ c (F c))
      → _⊑_ (F (μ F)) (μ F)
    μ-unfold-right-infl F SC inflF =
      μ-unfold-right F SC (iter-mono-chain-infl F inflF)

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
