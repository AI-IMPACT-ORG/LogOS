{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ProfileTowerFO where

-- A first-order (formula-coded) upgrade tower for ZF/ZFC stacks.
--
-- This module is intentionally conservative and epistemically strict:
-- - the upgrades here are *assumption boundaries*, not derivations of ZF(C)
--   schemata from weaker axioms;
-- - the goal is to make “schema strength” explicit by requiring coded
--   `Formula`s (rather than Agda predicates/relations) at the interface.
--
-- In the stack-first ZFC route, this FO tower is the canonical place where
-- Separation/Replacement live: they are assumed only for *formula-coded*
-- predicates/relations, and they are packaged as explicit `View`s into the set
-- boundary preorder.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.View using (View; μ)

import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.ZFC as ZFC
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Proof.Syntax as Syn

-- ------------------------------------------------------------------------
-- First-order evaluation (definitions, not axioms).

FOValuation : ∀ {ℓ : Level} → (SetU : Set ℓ) → Set ℓ
FOValuation SetU = ℕ → SetU

extendFO : ∀ {ℓ : Level} {SetU : Set ℓ} → SetU → FOValuation SetU → FOValuation SetU
extendFO x ρ zero = x
extendFO x ρ (suc n) = ρ n

-- Utilities: formula evaluation for a `ZFStackBase`.

module ForBase {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) where
  open Tower.ZFStackBase B
  -- First-order valuations for the internal universe.
  Valuation : Set ℓ
  Valuation = FOValuation SetU

  extend : SetU → Valuation → Valuation
  extend = extendFO

  -- Derived successor and its membership specification from the core profile.
  module D = ZF.DerivedCore coreSig

  -- Constructor objects (as sets in `SetU`).
  emptySet : SetU
  emptySet = μ EmptyV tt

  pairSet : SetU → SetU → SetU
  pairSet x y = μ PairV (x , y)

  unionSet : SetU → SetU
  unionSet x = μ UnionV x

  powersetSet : SetU → SetU
  powersetSet x = μ PowersetV x

  omegaSet : SetU
  omegaSet = μ OmegaV tt

  zeroSet : SetU
  zeroSet = μ D.ZeroV tt

  succSet : SetU → SetU
  succSet x = μ D.SuccV x

  succ-spec : ∀ x z → (z ∈ succSet x) ↔ ((z ∈ x) ⊎ (z ≈ x))
  succ-spec = ZF.succ-spec-from-core coreSig coreLaws

  -- Term semantics for the constructor-extended first-order language.
  evalTerm : Syn.Term → Valuation → SetU
  evalTerm (Syn.var n) ρ = ρ n
  evalTerm Syn.emptyT ρ = emptySet
  evalTerm (Syn.pairT t u) ρ =
    pairSet (evalTerm t ρ) (evalTerm u ρ)
  evalTerm (Syn.unionT t) ρ = unionSet (evalTerm t ρ)
  evalTerm (Syn.powerT t) ρ = powersetSet (evalTerm t ρ)
  evalTerm (Syn.succT t) ρ = succSet (evalTerm t ρ)
  evalTerm Syn.omegaT ρ = omegaSet

  -- Formula semantics for the constructor-extended first-order language.
  evalFormula : Syn.Formula → Valuation → Set ℓ
  evalFormula Syn.⊥F ρ = ⊥
  evalFormula (t Syn.∈F u) ρ = evalTerm t ρ ∈ evalTerm u ρ
  evalFormula (t Syn.≈F u) ρ = evalTerm t ρ ≈ evalTerm u ρ
  evalFormula (φ Syn.⇒ ψ) ρ = evalFormula φ ρ → evalFormula ψ ρ
  evalFormula (φ Syn.∧F ψ) ρ = evalFormula φ ρ × evalFormula ψ ρ
  evalFormula (φ Syn.∨F ψ) ρ = evalFormula φ ρ ⊎ evalFormula ψ ρ
  evalFormula (φ Syn.↔F ψ) ρ = evalFormula φ ρ ↔ evalFormula ψ ρ
  evalFormula (Syn.∀F φ) ρ = ∀ x → evalFormula φ (extend x ρ)
  evalFormula (Syn.∃F φ) ρ = Σ SetU (λ x → evalFormula φ (extend x ρ))

  FunctionalOnX : Syn.Formula → Valuation → SetU → Set ℓ
  FunctionalOnX R ρ x =
    ∀ u
    → u ∈ x
    → Σ SetU
        (λ z →
          evalFormula R (extend u (extend z ρ))
            × (∀ z′ →
                  evalFormula R (extend u (extend z′ ρ))
                    → z′ ≈ z))

-- ------------------------------------------------------------------------
-- FO upgrades: formula-coded Separation/Replacement as transformer views.

record SeparationFOUpgrade {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) : Set (lsuc ℓ) where
  open Tower.ZFStackBase B
  module FB = ForBase B

  field
    SeparationFV
      : (P : Syn.Formula)
      → (ρ : FB.Valuation)
      → View SetU SetBnd

    separationF-spec
      : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x z : SetU)
      → (z ∈ μ (SeparationFV P ρ) x)
          ↔ ((z ∈ x) × FB.evalFormula P (FB.extend z (FB.extend x ρ)))

record ReplacementFOUpgrade {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) : Set (lsuc ℓ) where
  open Tower.ZFStackBase B
  module FB = ForBase B

  ReplacementCode : Syn.Formula → FB.Valuation → Set ℓ
  ReplacementCode R ρ = Σ SetU (λ x → FB.FunctionalOnX R ρ x)

  field
    ReplacementFV
      : (R : Syn.Formula)
      → (ρ : FB.Valuation)
      → View (ReplacementCode R ρ) SetBnd

    replacementF-spec
      : ∀ (R : Syn.Formula) (ρ : FB.Valuation)
      → ∀ (x : SetU)
      → (fun : FB.FunctionalOnX R ρ x)
      → ∀ z
      → (z ∈ μ (ReplacementFV R ρ) (x , fun))
        ↔ (Σ SetU (λ u → u ∈ x × FB.evalFormula R (FB.extend u (FB.extend z ρ))))

pairingStackFromBase : ∀ {ℓ : Level} → Tower.ZFStackBase {ℓ} → ZFC.ZFPairingStack {ℓ}
pairingStackFromBase B =
  record
    { ctx = Tower.ZFStackBase.ctx B
    ; sig = Tower.ZFStackBase.coreSig B
    ; laws = Tower.ZFStackBase.coreLaws B
    }

-- ------------------------------------------------------------------------
-- Bundled FO stacks (stack-first surface; Separation/Replacement are FO-coded).

record ZFStackFOCore {ℓ : Level} : Set (lsuc ℓ) where
  field
    base : Tower.ZFStackBase {ℓ}
    sep  : SeparationFOUpgrade base
    rep  : ReplacementFOUpgrade base

  open Tower.ZFStackBase base public
  open SeparationFOUpgrade sep public using (SeparationFV; separationF-spec)
  open ReplacementFOUpgrade rep public using (ReplacementCode; ReplacementFV; replacementF-spec)

  module Base = ForBase base

mkZFStackFOCore
  : ∀ {ℓ : Level}
  → (base : Tower.ZFStackBase {ℓ})
  → SeparationFOUpgrade base
  → ReplacementFOUpgrade base
  → ZFStackFOCore {ℓ}
mkZFStackFOCore base sep rep =
  record
    { base = base
    ; sep = sep
    ; rep = rep
    }

record ZFStackFO₋Fnd {ℓ : Level} : Set (lsuc ℓ) where
  field
    core : ZFStackFOCore {ℓ}

  open ZFStackFOCore core public

record ZFStackFO {ℓ : Level} : Set (lsuc ℓ) where
  field
    core : ZFStackFOCore {ℓ}
    fnd  : Tower.FoundationUpgrade (ZFStackFOCore.base core)

  open ZFStackFOCore core public
  open Tower.FoundationUpgrade fnd public

forgetFoundation
  : ∀ {ℓ : Level}
  → ZFStackFO {ℓ}
  → ZFStackFO₋Fnd {ℓ}
forgetFoundation zf =
  record
    { core = ZFStackFO.core zf
    }

record ZFCStackFO₋Fnd {ℓ : Level} : Set (lsuc ℓ) where
  field
    zf : ZFStackFO₋Fnd {ℓ}
    choice : Tower.ChoiceUpgrade (pairingStackFromBase (ZFStackFO₋Fnd.base zf))

  open ZFStackFO₋Fnd zf public
  open Tower.ChoiceUpgrade choice public
record ZFCStackFO {ℓ : Level} : Set (lsuc ℓ) where
  field
    zf : ZFStackFO {ℓ}
    choice : Tower.ChoiceUpgrade (pairingStackFromBase (ZFStackFO.base zf))

  open ZFStackFO zf public
  open Tower.ChoiceUpgrade choice public
