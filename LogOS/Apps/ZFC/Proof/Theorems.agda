{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Theorems where

open import LogOS.Prelude
import LogOS.Apps.ZFC.Proof.Syntax as Syntax
open Syntax
import LogOS.Apps.ZFC.Proof.Axioms as Axioms
open Axioms
import LogOS.Apps.ZFC.Proof.System as Sys

logicStep : ∀ {Γ φ} → LogicEqAxiom φ → Sys.Derives TheoryAxiom Γ φ
logicStep l = Sys.axiom (axLogic l)

logicStepC : ∀ {Γ φ} → LogicEqAxiom φ → Sys.Derives TheoryCAxiom Γ φ
logicStepC l = Sys.axiom (axLogicC l)

zfStep : ∀ {Γ φ} → ZFAxiom φ → Sys.Derives TheoryAxiom Γ φ
zfStep z = Sys.axiom (axZFCore z)

zfcStep : ∀ {Γ φ} → ZFCAxiom φ → Sys.Derives TheoryCAxiom Γ φ
zfcStep z = Sys.axiom (axZFCCore z)

logicStepE : ∀ {Γ φ} → LogicEqAxiomExt φ → Sys.Derives TheoryAxiomExt Γ φ
logicStepE l = Sys.axiom (axLogicE l)

logicStepCE : ∀ {Γ φ} → LogicEqAxiomExt φ → Sys.Derives TheoryCAxiomExt Γ φ
logicStepCE l = Sys.axiom (axLogicCE l)

zfStepE : ∀ {Γ φ} → ZFAxiom φ → Sys.Derives TheoryAxiomExt Γ φ
zfStepE z = Sys.axiom (axZFCoreE z)

zfcStepE : ∀ {Γ φ} → ZFCAxiom φ → Sys.Derives TheoryCAxiomExt Γ φ
zfcStepE z = Sys.axiom (axZFCCoreE z)

module LogicDerived
  {Ax : Formula → Set}
  (logicStep′ : ∀ {Γ φ} → LogicEqAxiom φ → Sys.Derives Ax Γ φ)
  where

  iffElimL
    : ∀ {Γ φ ψ}
    → Sys.Derives Ax Γ (φ ↔F ψ)
    → Sys.Derives Ax Γ φ
    → Sys.Derives Ax Γ ψ
  iffElimL {φ = φ} {ψ = ψ} dIff dφ =
    Sys.mp
      (Sys.mp (logicStep′ (axIffElimL φ ψ)) dIff)
      dφ

  iffElimR
    : ∀ {Γ φ ψ}
    → Sys.Derives Ax Γ (φ ↔F ψ)
    → Sys.Derives Ax Γ ψ
    → Sys.Derives Ax Γ φ
  iffElimR {φ = φ} {ψ = ψ} dIff dψ =
    Sys.mp
      (Sys.mp (logicStep′ (axIffElimR φ ψ)) dIff)
      dψ

  allElim
    : ∀ {Γ φ}
    → (t : Term)
    → Sys.Derives Ax Γ (∀F φ)
    → Sys.Derives Ax Γ (subst0Formula t φ)
  allElim {φ = φ} t dAll =
    Sys.mp (logicStep′ (axAllElim φ t)) dAll

  allImp
    : ∀ {Γ φ ψ}
    → Sys.Derives Ax Γ (∀F (φ ⇒ ψ))
    → Sys.Derives Ax Γ (∀F φ)
    → Sys.Derives Ax Γ (∀F ψ)
  allImp {φ = φ} {ψ = ψ} dAllImp dAllφ =
    Sys.mp
      (Sys.mp (logicStep′ (axAllImp φ ψ)) dAllImp)
      dAllφ

  allIntro
    : ∀ {Γ A φ}
    → Sys.Derives Ax Γ (∀F ((liftFormula A) ⇒ φ))
    → Sys.Derives Ax Γ A
    → Sys.Derives Ax Γ (∀F φ)
  allIntro {A = A} {φ = φ} dAllImp dA =
    Sys.mp
      (Sys.mp (logicStep′ (axAllIntro A φ)) dAllImp)
      dA

  exIntro
    : ∀ {Γ φ}
    → (t : Term)
    → Sys.Derives Ax Γ (subst0Formula t φ)
    → Sys.Derives Ax Γ (∃F φ)
  exIntro {φ = φ} t dφ =
    Sys.mp (logicStep′ (axExIntro φ t)) dφ

  exElim
    : ∀ {Γ φ A}
    → Sys.Derives Ax Γ (∀F (φ ⇒ liftFormula A))
    → Sys.Derives Ax Γ (∃F φ)
    → Sys.Derives Ax Γ A
  exElim {φ = φ} {A = A} dAllImp dEx =
    Sys.mp
      (Sys.mp (logicStep′ (axExElim φ A)) dAllImp)
      dEx

  eqRefl
    : ∀ {Γ} (t : Term)
    → Sys.Derives Ax Γ (t ≈F t)
  eqRefl t = logicStep′ (axEqRefl t)

  eqSym
    : ∀ {Γ} (t u : Term)
    → Sys.Derives Ax Γ (t ≈F u)
    → Sys.Derives Ax Γ (u ≈F t)
  eqSym t u dEq =
    Sys.mp (logicStep′ (axEqSym t u)) dEq

  eqTrans
    : ∀ {Γ} (t u v : Term)
    → Sys.Derives Ax Γ (t ≈F u)
    → Sys.Derives Ax Γ (u ≈F v)
    → Sys.Derives Ax Γ (t ≈F v)
  eqTrans t u v dTU dUV =
    Sys.mp
      (Sys.mp (logicStep′ (axEqTrans t u v)) dTU)
      dUV

  memExt
    : ∀ {Γ} (t u v : Term)
    → Sys.Derives Ax Γ (u ≈F v)
    → Sys.Derives Ax Γ ((t ∈F u) ↔F (t ∈F v))
  memExt t u v dEq =
    Sys.mp (logicStep′ (axMemExt t u v)) dEq

  memCongR
    : ∀ {Γ} (t u v : Term)
    → Sys.Derives Ax Γ (u ≈F v)
    → Sys.Derives Ax Γ (t ∈F u)
    → Sys.Derives Ax Γ (t ∈F v)
  memCongR t u v dEq dMem =
    iffElimL (memExt t u v dEq) dMem

  memCongL
    : ∀ {Γ} (t u v : Term)
    → Sys.Derives Ax Γ (u ≈F v)
    → Sys.Derives Ax Γ (t ∈F v)
    → Sys.Derives Ax Γ (t ∈F u)
  memCongL t u v dEq dMem =
    iffElimR (memExt t u v dEq) dMem

module LogicZF = LogicDerived {Ax = TheoryAxiom} logicStep
module LogicZFC = LogicDerived {Ax = TheoryCAxiom} logicStepC

module LogicZFExt =
  LogicDerived
    {Ax = TheoryAxiomExt}
    (λ l → logicStepE (axBase l))

module LogicZFCExt =
  LogicDerived
    {Ax = TheoryCAxiomExt}
    (λ l → logicStepCE (axBase l))

memCongLTheoremE
  : ∀ {Γ} (t u v : Term)
  → Sys.Derives TheoryAxiomExt Γ (t ≈F u)
  → Sys.Derives TheoryAxiomExt Γ (t ∈F v)
  → Sys.Derives TheoryAxiomExt Γ (u ∈F v)
memCongLTheoremE t u v dEq dMem =
  LogicZFExt.iffElimL
    (Sys.mp (logicStepE (axMemCongL t u v)) dEq)
    dMem

-- Nontrivial Hilbert derivation: φ ⇒ φ from K and S.

idTheorem : ∀ {φ} → Sys.Theorem TheoryAxiom (φ ⇒ φ)
idTheorem {φ} =
  Sys.mp
    (Sys.mp
      (logicStep (axS φ (φ ⇒ φ) φ))
      (logicStep (axK φ (φ ⇒ φ))))
    (logicStep (axK φ φ))

idTheoremC : ∀ {φ} → Sys.Theorem TheoryCAxiom (φ ⇒ φ)
idTheoremC {φ} =
  Sys.mp
    (Sys.mp
      (logicStepC (axS φ (φ ⇒ φ) φ))
      (logicStepC (axK φ (φ ⇒ φ))))
    (logicStepC (axK φ φ))

-- Basic propositional consistency checks (directly as logic axioms).

⊥-elimTheorem : ∀ {φ} → Sys.Theorem TheoryAxiom (⊥F ⇒ φ)
⊥-elimTheorem {φ} = logicStep (axBottom φ)

∧-proj₁Theorem : ∀ {φ ψ} → Sys.Theorem TheoryAxiom ((φ ∧F ψ) ⇒ φ)
∧-proj₁Theorem {φ} {ψ} = logicStep (axAndElimL φ ψ)

∧-proj₂Theorem : ∀ {φ ψ} → Sys.Theorem TheoryAxiom ((φ ∧F ψ) ⇒ ψ)
∧-proj₂Theorem {φ} {ψ} = logicStep (axAndElimR φ ψ)

kTheorem : ∀ {φ ψ} → Sys.Theorem TheoryAxiom (K φ ψ)
kTheorem {φ} {ψ} = logicStep (axK φ ψ)

extensionalityTheorem : Sys.Theorem TheoryAxiom extensionalityF
extensionalityTheorem = zfStep axExtensionality

pairingTheorem : Sys.Theorem TheoryAxiom pairingF
pairingTheorem = zfStep axPairing

foundationTheorem : Sys.Theorem TheoryAxiom foundationF
foundationTheorem = zfStep axFoundation

separationSchemaTheorem : (P : Formula) → Sys.Theorem TheoryAxiom (separationSchemaF P)
separationSchemaTheorem P = zfStep (axSeparationSchema P)

replacementSchemaTheorem : (R : Formula) → Sys.Theorem TheoryAxiom (replacementSchemaF R)
replacementSchemaTheorem R = zfStep (axReplacementSchema R)

choiceTheorem : Sys.Theorem TheoryCAxiom choiceF
choiceTheorem = zfcStep axChoice
