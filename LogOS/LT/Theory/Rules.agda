{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theory.Rules where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Theories closed under an explicit rule set (Metamath-style assertions).
--
-- This generalises `LogOS.LT.Theory.HilbertMP` from a single binary rule (modus
-- ponens) to arbitrary finitary rules given by a list of premises + a
-- conclusion.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_)
open import LogOS.LT.Flow using (GuardedClosure; Stable; stable)
open import LogOS.LT.Reflection using (quot; evalm; evalm∘quot⊑Flow; Flow⊑evalm∘quot)
open import LogOS.LT.AbstractKZ using (KZModality)
open import LogOS.LT.Effectivity using (Effectivity)

-- A finitary rule as a list of premises + a conclusion.
record RuleSpec {ℓ : Level} (Formula : Set ℓ) : Set ℓ where
  field
    premises   : List Formula
    conclusion : Formula

module RuleClosure
  {ℓ : Level}
  (Formula : Set ℓ)
  (Rule : Set ℓ)
  (spec : Rule → RuleSpec Formula)
  where

  premises : Rule → List Formula
  premises r = RuleSpec.premises (spec r)

  conclusion : Rule → Formula
  conclusion r = RuleSpec.conclusion (spec r)

  -- A theory is a predicate on formulas.
  Theory : Set (lsuc ℓ)
  Theory = Formula → Set ℓ

  -- Inclusion (monotone w.r.t. the LogOS polarity: right side stronger).
  infix 4 _⊑T_
  _⊑T_ : Theory → Theory → Set ℓ
  T ⊑T U = ∀ φ → T φ → U φ

  -- The preorder of theories by inclusion.
  TheoryPreorder : ConPreorder (lsuc ℓ) ℓ
  TheoryPreorder =
    record
      { Con   = Theory
      ; _⊑_   = _⊑T_
      ; refl  = λ {T} φ t → t
      ; trans = λ {T} {U} {V} TU UV φ t → UV φ (TU φ t)
      }

  -- Heterogeneous list of premise proofs.
  data All (P : Formula → Set ℓ) : List Formula → Set ℓ where
    all[] : All P []
    all∷  : ∀ {φ Γ} → P φ → All P Γ → All P (φ ∷ Γ)

  -- Derivability from a theory predicate under an explicit rule set.
  data DerivesR (Base : Formula → Set ℓ) (T : Theory) : Formula → Set ℓ where
    hypT   : ∀ {φ} → T φ → DerivesR Base T φ
    axiomT : ∀ {φ} → Base φ → DerivesR Base T φ
    ruleT  : (r : Rule) → All (DerivesR Base T) (premises r) → DerivesR Base T (conclusion r)

  -- Closure operator: deductive closure of a theory under `DerivesR`.
  FlowTheory : (Formula → Set ℓ) → Theory → Theory
  FlowTheory Base T φ = DerivesR Base T φ

  mapDerivesR
    : ∀ {Base : Formula → Set ℓ} {T U : Theory}
    → T ⊑T U
    → ∀ {φ} → DerivesR Base T φ → DerivesR Base U φ
  mapDerivesR TU d = go TU d
    where
      mutual
        go : ∀ {Base : Formula → Set ℓ} {T U : Theory} {φ}
          → T ⊑T U
          → DerivesR Base T φ
          → DerivesR Base U φ
        go TU (hypT t) = hypT (TU _ t)
        go TU (axiomT b) = axiomT b
        go TU (ruleT r ps) = ruleT r (goAll TU ps)

        goAll : ∀ {Base : Formula → Set ℓ} {T U : Theory} {Γ}
          → T ⊑T U
          → All (DerivesR Base T) Γ
          → All (DerivesR Base U) Γ
        goAll TU all[] = all[]
        goAll TU (all∷ p ps) = all∷ (go TU p) (goAll TU ps)

  -- Idempotence (lax): closing under already-closed axioms does not add power.
  FlowTheory-idemp-lax
    : ∀ (Base : Formula → Set ℓ) (T : Theory) {φ : Formula}
    → FlowTheory Base (FlowTheory Base T) φ
    → FlowTheory Base T φ
  FlowTheory-idemp-lax Base T d = go d
    where
      mutual
        go : ∀ {φ} → FlowTheory Base (FlowTheory Base T) φ → FlowTheory Base T φ
        go (hypT d) = d
        go (axiomT b) = axiomT b
        go (ruleT r ps) = ruleT r (goAll ps)

        goAll
          : ∀ {Γ}
          → All (FlowTheory Base (FlowTheory Base T)) Γ
          → All (FlowTheory Base T) Γ
        goAll all[] = all[]
        goAll (all∷ p ps) = all∷ (go p) (goAll ps)

  -- Guarded closure (KZ modality) on theories: "deductive closure".
  theoryClosure
    : (Base : Formula → Set ℓ)
    → GuardedClosure TheoryPreorder
  theoryClosure Base =
    record
      { Flow =
          FlowTheory Base
      ; mono =
          λ {T} {U} TU φ d →
            mapDerivesR {Base = Base} TU d
      ; infl =
          λ T φ t → hypT t
      ; idemp-lax =
          λ T φ d → FlowTheory-idemp-lax Base T d
      }

  theoryKZ : (Base : Formula → Set ℓ) → KZModality TheoryPreorder
  theoryKZ Base =
    record { GC = theoryClosure Base }

  theoryEffectivity
    : (Base : Formula → Set ℓ)
    → Effectivity TheoryPreorder
  theoryEffectivity Base =
    record { GC = theoryClosure Base }

  -- Deductively closed theories (stable points) and their reflection interface.
  ClosedTheory
    : (Base : Formula → Set ℓ)
    → Set (lsuc (lsuc ℓ))
  ClosedTheory Base = Stable {CP = TheoryPreorder} (FlowTheory Base)

  closeTheory
    : (Base : Formula → Set ℓ)
    → Theory
    → ClosedTheory Base
  closeTheory Base = quot (theoryClosure Base)

  theoryOf : ∀ {Base : Formula → Set ℓ} → ClosedTheory Base → Theory
  theoryOf {Base} = evalm {GC = theoryClosure Base}

  closeTheory-eval⊑FlowTheory
    : ∀ (Base : Formula → Set ℓ) (T : Theory)
    → _⊑_ TheoryPreorder (theoryOf {Base = Base} (closeTheory Base T)) (FlowTheory Base T)
  closeTheory-eval⊑FlowTheory Base T =
    evalm∘quot⊑Flow (theoryClosure Base) T

  FlowTheory⊑closeTheory-eval
    : ∀ (Base : Formula → Set ℓ) (T : Theory)
    → _⊑_ TheoryPreorder (FlowTheory Base T) (theoryOf {Base = Base} (closeTheory Base T))
  FlowTheory⊑closeTheory-eval Base T =
    Flow⊑evalm∘quot (theoryClosure Base) T

  closeTheory-eval≈FlowTheory
    : ∀ (Base : Formula → Set ℓ) (T : Theory)
    → _≈_ TheoryPreorder (theoryOf {Base = Base} (closeTheory Base T)) (FlowTheory Base T)
  closeTheory-eval≈FlowTheory Base T =
    (closeTheory-eval⊑FlowTheory Base T , FlowTheory⊑closeTheory-eval Base T)

  closed-elim
    : ∀ {Base : Formula → Set ℓ} (U : ClosedTheory Base) {φ : Formula}
    → DerivesR Base (theoryOf U) φ
    → theoryOf U φ
  closed-elim {Base = Base} U {φ} d = stable U φ d

  closed-intro
    : ∀ {Base : Formula → Set ℓ} (U : ClosedTheory Base) {φ : Formula}
    → theoryOf U φ
    → DerivesR Base (theoryOf U) φ
  closed-intro U u = hypT u
