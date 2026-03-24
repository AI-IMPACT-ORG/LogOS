{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Axioms where

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
import LogOS.Apps.ZFC.Proof.Syntax as Syntax
open Syntax

K : Formula → Formula → Formula
K φ ψ = φ ⇒ (ψ ⇒ φ)

S : Formula → Formula → Formula → Formula
S φ ψ χ = (φ ⇒ (ψ ⇒ χ)) ⇒ ((φ ⇒ ψ) ⇒ (φ ⇒ χ))

-- Closed ZF/ZFC core formulas over the constructor language.

extensionalityF : Formula
extensionalityF =
  ∀F (∀F
    ((∀F ((v0 ∈F v2) ↔F (v0 ∈F v1)))
      ⇒ (v1 ≈F v0)))

emptyF : Formula
emptyF = ∀F (¬F (v0 ∈F emptyT))

pairingF : Formula
pairingF =
  ∀F (∀F (∀F
    ((v0 ∈F pairT v2 v1)
      ↔F ((v0 ≈F v2) ∨F (v0 ≈F v1)))))

unionF : Formula
unionF =
  ∀F (∀F
    ((v0 ∈F unionT v1)
      ↔F (∃F ((v0 ∈F v2) ∧F (v1 ∈F v0)))))

powersetF : Formula
powersetF =
  ∀F (∀F
    ((v0 ∈F powerT v1)
      ↔F (∀F ((v0 ∈F v1) ⇒ (v0 ∈F v2)))))

succF : Formula
succF =
  ∀F (∀F
    ((v0 ∈F succT v1)
      ↔F ((v0 ∈F v1) ∨F (v0 ≈F v1))))

infinityF : Formula
infinityF =
  ∀F
    ((v0 ∈F omegaT)
      ↔F ((v0 ≈F emptyT)
        ∨F (∃F ((v0 ∈F omegaT) ∧F (v1 ≈F succT v0)))))

foundationF : Formula
foundationF =
  ∀F
    ( (∃F (v0 ∈F v1))
      ⇒ (∃F
          ((v0 ∈F v1)
            ∧F (∀F ((v0 ∈F v2) ⇒ ¬F (v0 ∈F v1))))))

-- Object-language schema representatives.
-- Conventions:
-- - in `separationSchemaF P`, `P` is read in context `(z , x , params...)`
--   (`z` at index 0, base set `x` at index 1). The witness set binder is
--   inserted structurally via `liftAfter0Formula`.
-- - in `replacementSchemaF R`, `R` is read in context `(u , z , params...)`
--   (`u` at index 0, image element `z` at index 1).
--   The schema asserts functional totality of `R` on `x`, then forms the image
--   set `{ z | ∃ u ∈ x . R u z }`.

separationSchemaF : Formula → Formula
separationSchemaF P =
  ∀F (∃F (∀F
    ((v0 ∈F v1) ↔F ((v0 ∈F v2) ∧F liftAfter0Formula P))))

functionalOnXReplacementF : Formula → Formula

replacementSchemaF : Formula → Formula
replacementSchemaF R =
  ∀F
    ( functionalOnXReplacementF R
      ⇒ ∃F (∀F
          ((v0 ∈F v1)
            ↔F (∃F ((v0 ∈F v3) ∧F renameFormula insertAfter1By2Ren R))))
    )

-- Helper subformulas used by `replacementSchemaF`.
--
-- These are defined at top level so the semantic soundness proof can reuse
-- them definitionally when unpacking the functional premise.

-- Context under `∃ z` (inside `∀ u`):
--   `z` at 0, `u` at 1, `x` at 2.
R-exists : Formula → Formula
R-exists R = renameFormula insertAfter1Ren (renameFormula swap01Ren R)

-- Context under `∀ z1 . ∀ z2` (inside `∀ u`):
--   `z2` at 0, `z1` at 1, `u` at 2, `x` at 3.
R-u-z1Ren : Renaming
R-u-z1Ren zero = suc (suc zero)                -- u
R-u-z1Ren (suc zero) = suc zero                -- z1
R-u-z1Ren (suc (suc n)) = suc (suc (suc (suc n))) -- params (+2)

R-u-z2Ren : Renaming
R-u-z2Ren zero = suc (suc zero)                -- u
R-u-z2Ren (suc zero) = zero                    -- z2
R-u-z2Ren (suc (suc n)) = suc (suc (suc (suc n))) -- params (+2)

R-u-z1 : Formula → Formula
R-u-z1 R = renameFormula R-u-z1Ren R

R-u-z2 : Formula → Formula
R-u-z2 R = renameFormula R-u-z2Ren R

-- Context: `x` at index 0.
--
-- Functional premise: for every `u ∈ x` there exists a unique `z` (up to `≈F`)
-- such that `R u z`.
functionalOnXReplacementF R =
  ∀F
    ( (v0 ∈F v1)
      ⇒ ( (∃F (R-exists R))
        ∧F (∀F (∀F (((R-u-z1 R) ∧F (R-u-z2 R)) ⇒ (v1 ≈F v0))))
        )
    )

-- Standard (non-global-choice) AC as a single object-language axiom:
-- every family of nonempty sets has a choice function (as a Kuratowski-graph).

singletonT : Term → Term
singletonT t = pairT t t

opairT : Term → Term → Term
opairT x y = pairT (singletonT x) (pairT x y)

choiceFunctionOnF : Formula
choiceFunctionOnF =
  ( domF ∧F totF ) ∧F funF
  where
    -- Context: `f` at index 0, `X` at index 1.

    domF : Formula
    domF =
      ∀F (∀F
        ((opairT v1 v0 ∈F v2) ⇒ (v1 ∈F v3)))

    totF : Formula
    totF =
      ∀F
        ((v0 ∈F v2)
          ⇒ (∃F
              ((opairT v1 v0 ∈F v2)
                ∧F (v0 ∈F v1))))

    funF : Formula
    funF =
      ∀F (∀F (∀F
        ((opairT v2 v1 ∈F v3)
          ⇒ ((opairT v2 v0 ∈F v3)
            ⇒ (v1 ≈F v0)))))

nonemptyFamilyF : Formula
nonemptyFamilyF =
  -- Context: `X` at index 0.
  ∀F
    ((v0 ∈F v1)
      ⇒ (∃F (v0 ∈F v1)))

choiceF : Formula
choiceF =
  ∀F
    ( nonemptyFamilyF
      ⇒ (∃F choiceFunctionOnF)
    )

data LogicEqAxiom : Formula → Set where
  axK : ∀ φ ψ → LogicEqAxiom (K φ ψ)
  axS : ∀ φ ψ χ → LogicEqAxiom (S φ ψ χ)
  -- Standard propositional structure (Hilbert-style combinators).
  --
  -- These are kept explicit: `Proof.System` only has modus ponens as a rule,
  -- so the logical connectives must be given their introduction/elimination
  -- power by axioms (Metamath-style).
  axBottom : ∀ φ → LogicEqAxiom (⊥F ⇒ φ)

  axAndIntro : ∀ φ ψ → LogicEqAxiom (φ ⇒ (ψ ⇒ (φ ∧F ψ)))
  axAndElimL : ∀ φ ψ → LogicEqAxiom ((φ ∧F ψ) ⇒ φ)
  axAndElimR : ∀ φ ψ → LogicEqAxiom ((φ ∧F ψ) ⇒ ψ)

  axOrIntroL : ∀ φ ψ → LogicEqAxiom (φ ⇒ (φ ∨F ψ))
  axOrIntroR : ∀ φ ψ → LogicEqAxiom (ψ ⇒ (φ ∨F ψ))
  axOrElim : ∀ φ ψ χ → LogicEqAxiom ((φ ⇒ χ) ⇒ ((ψ ⇒ χ) ⇒ ((φ ∨F ψ) ⇒ χ)))

  axIffIntro : ∀ φ ψ → LogicEqAxiom ((φ ⇒ ψ) ⇒ ((ψ ⇒ φ) ⇒ (φ ↔F ψ)))
  axIffElimL : ∀ φ ψ → LogicEqAxiom ((φ ↔F ψ) ⇒ (φ ⇒ ψ))
  axIffElimR : ∀ φ ψ → LogicEqAxiom ((φ ↔F ψ) ⇒ (ψ ⇒ φ))

  -- First-order structure (quantifiers) in de Bruijn form.
  --
  -- Variable discipline is made explicit:
  -- - instantiation uses `subst0Formula`,
  -- - side conditions ("x not free in A") are represented by weakening
  --   (`liftFormula A`) under the binder.
  axAllElim : ∀ φ t → LogicEqAxiom ((∀F φ) ⇒ subst0Formula t φ)
  axAllImp : ∀ φ ψ → LogicEqAxiom ((∀F (φ ⇒ ψ)) ⇒ ((∀F φ) ⇒ (∀F ψ)))
  axAllIntro : ∀ A φ → LogicEqAxiom ((∀F ((liftFormula A) ⇒ φ)) ⇒ (A ⇒ (∀F φ)))

  axExIntro : ∀ φ t → LogicEqAxiom (subst0Formula t φ ⇒ (∃F φ))
  axExElim : ∀ φ A → LogicEqAxiom ((∀F (φ ⇒ liftFormula A)) ⇒ ((∃F φ) ⇒ A))

  -- Extensional equality induced by membership: `x ≈ y` means mutual inclusion.
  axEqSym : ∀ t u → LogicEqAxiom ((t ≈F u) ⇒ (u ≈F t))
  axEqTrans : ∀ t u v → LogicEqAxiom ((t ≈F u) ⇒ ((u ≈F v) ⇒ (t ≈F v)))
  axMemExt : ∀ t u v → LogicEqAxiom ((u ≈F v) ⇒ ((t ∈F u) ↔F (t ∈F v)))

  axEqRefl : ∀ t → LogicEqAxiom (t ≈F t)

-- Optional strengthening: treat `≈F` as full first-order equality by adding
-- substitutivity/congruence principles.
--
-- This is *not* sound in arbitrary `≈`-models: it becomes sound once the model
-- has canonical representatives / an extensional quotient, i.e. `x ≈ y → x ≡ y`
-- at the semantic level.

data LogicEqAxiomExt : Formula → Set where
  axBase : ∀ {φ} → LogicEqAxiom φ → LogicEqAxiomExt φ

  -- Equality substitution into the *element* position of membership.
  --
  -- (The set-position congruence is already `axMemExt` in `LogicEqAxiom`.)
  axMemCongL : ∀ t u v → LogicEqAxiomExt ((t ≈F u) ⇒ ((t ∈F v) ↔F (u ∈F v)))

  -- Congruence for the primitive term constructors (function symbols).
  axPairCongL : ∀ t u v → LogicEqAxiomExt ((t ≈F u) ⇒ (pairT t v ≈F pairT u v))
  axPairCongR : ∀ t u v → LogicEqAxiomExt ((t ≈F u) ⇒ (pairT v t ≈F pairT v u))
  axUnionCong : ∀ t u → LogicEqAxiomExt ((t ≈F u) ⇒ (unionT t ≈F unionT u))
  axPowerCong : ∀ t u → LogicEqAxiomExt ((t ≈F u) ⇒ (powerT t ≈F powerT u))
  axSuccCong : ∀ t u → LogicEqAxiomExt ((t ≈F u) ⇒ (succT t ≈F succT u))

data ZFAxiom : Formula → Set where
  axExtensionality : ZFAxiom extensionalityF
  axEmpty          : ZFAxiom emptyF
  axPairing        : ZFAxiom pairingF
  axUnion          : ZFAxiom unionF
  axPowerset       : ZFAxiom powersetF
  axSucc           : ZFAxiom succF
  axInfinity       : ZFAxiom infinityF
  axFoundation     : ZFAxiom foundationF
  axSeparationSchema : (P : Formula) → ZFAxiom (separationSchemaF P)
  axReplacementSchema : (R : Formula) → ZFAxiom (replacementSchemaF R)

data ZFCAxiom : Formula → Set where
  axZF     : ∀ {φ} → ZFAxiom φ → ZFCAxiom φ
  axChoice : ZFCAxiom choiceF

data TheoryAxiom : Formula → Set where
  axLogic : ∀ {φ} → LogicEqAxiom φ → TheoryAxiom φ
  axZFCore : ∀ {φ} → ZFAxiom φ → TheoryAxiom φ

data TheoryCAxiom : Formula → Set where
  axLogicC : ∀ {φ} → LogicEqAxiom φ → TheoryCAxiom φ
  axZFCCore : ∀ {φ} → ZFCAxiom φ → TheoryCAxiom φ

data TheoryAxiomExt : Formula → Set where
  axLogicE : ∀ {φ} → LogicEqAxiomExt φ → TheoryAxiomExt φ
  axZFCoreE : ∀ {φ} → ZFAxiom φ → TheoryAxiomExt φ

data TheoryCAxiomExt : Formula → Set where
  axLogicCE : ∀ {φ} → LogicEqAxiomExt φ → TheoryCAxiomExt φ
  axZFCCoreE : ∀ {φ} → ZFCAxiom φ → TheoryCAxiomExt φ
