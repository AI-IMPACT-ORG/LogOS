{- 
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module docs.DeepDive.PLSpineSpine where

-- Minimal "mechanization spine" entry points: syntax, statics, dynamics.
-- This module does not add axioms; it only packages existing proofs.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.ObjectLogic.FOL.Syntax as FOLSyntax using (Signature; PredSym; RelSym₂; Term; Fml; Ctx)
open import LogOS.ObjectLogic.FOL.Subst as FOLSubst using (Ren; renameFml; inst; wkFml)
open import LogOS.ObjectLogic.FOL.ND using (Deriv)
import LogOS.ObjectLogic.FOL.Semantics as FOLSem
import LogOS.ObjectLogic.FOL.Soundness as FOLSound

open import LogOS.UniversalIR.While.Language as WhileLang using (Stmt; skip)
open import LogOS.UniversalIR.While.Semantics as WhileSem using (Exec; Store)
import LogOS.UniversalIR.While.Typing as WhileTyping
import LogOS.UniversalIR.While.SmallStep as WhileStep

module FOL
  {ℓΣ ℓ : Level}
  {Σ₀ : Signature {ℓΣ}}
  (D : Set ℓ)
  (PredI : PredSym Σ₀ → D → Set ℓ)
  (RelI : RelSym₂ Σ₀ → D → D → Set ℓ)
  where

  open FOLSem.For D PredI RelI

  rename-correct
    : ∀ {m n} (ρ : Ren m n) (env : Env n) (φ : Fml Σ₀ m)
    → Sat env (renameFml ρ φ) ↔ Sat (renEnv ρ env) φ
  rename-correct = sat-rename

  wk-correct
    : ∀ {n} (env : Env n) (d : D) (φ : Fml Σ₀ n)
    → Sat (extend d env) (wkFml φ) ↔ Sat env φ
  wk-correct = sat-wk

  subst-correct
    : ∀ {n} (env : Env n) (t : Term n) (φ : Fml Σ₀ (suc n))
    → Sat env (inst t φ) ↔ Sat (extend (env t) env) φ
  subst-correct = sat-inst

  soundness
    : ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
    → Deriv Γ φ
    → (env : Env n)
    → SatCtx env Γ
    → Sat env φ
  soundness = FOLSound.sound D PredI RelI

module While where

  Eff : Set
  Eff = WhileTyping.Eff

  VarEff : Set
  VarEff = WhileTyping.VarEff

  infix 4 _≤eff_

  _≤eff_ : Eff → Eff → Set
  _≤eff_ = WhileTyping._≤eff_

  StmtEff : Stmt → Eff → Set
  StmtEff = WhileTyping.StmtEff

  inferEff : Stmt → Eff
  inferEff = WhileTyping.inferEff

  StmtOk : Stmt → Set
  StmtOk = WhileTyping.StmtOk

  Step : Stmt → Store → Stmt → Store → Set
  Step = WhileStep.Step

  Steps : Stmt → Store → Stmt → Store → Set
  Steps = WhileStep.Steps

  progress-eff
    : ∀ {s σ e}
    → StmtEff s e
    → (s ≡ skip) ⊎ Σ Stmt (λ s' → Σ Store (λ σ' → Step s σ s' σ'))
  progress-eff = WhileStep.progress-eff

  progress
    : ∀ {s σ}
    → StmtOk s
    → (s ≡ skip) ⊎ Σ Stmt (λ s' → Σ Store (λ σ' → Step s σ s' σ'))
  progress = WhileStep.progress

  preservation
    : ∀ {s σ s' σ' e}
    → StmtEff s e
    → Step s σ s' σ'
    → Σ Eff (λ e' → StmtEff s' e' × e' ≤eff e)
  preservation = WhileStep.preservation

  preservation-bounded
    : ∀ {s σ s' σ' e}
    → StmtEff s e
    → Step s σ s' σ'
    → Σ Eff (λ e' → StmtEff s' e' × e' ≤eff e)
  preservation-bounded = WhileStep.preservation-bounded

  preservation-ok
    : ∀ {s σ s' σ'}
    → StmtOk s
    → Step s σ s' σ'
    → StmtOk s'
  preservation-ok = WhileStep.preservation-ok

  deterministic
    : ∀ {s σ s₁ σ₁ s₂ σ₂}
    → Step s σ s₁ σ₁
    → Step s σ s₂ σ₂
    → s₁ ≡ s₂ × σ₁ ≡ σ₂
  deterministic = WhileStep.deterministic

  exec→steps
    : ∀ {s σ σ'}
    → Exec s σ σ'
    → Steps s σ skip σ'
  exec→steps = WhileStep.exec→steps

  steps→exec
    : ∀ {s σ σ'}
    → Steps s σ skip σ'
    → Exec s σ σ'
  steps→exec = WhileStep.steps→exec

  -- Big-step determinism for terminating executions.
  exec-deterministic
    : ∀ {s σ σ₁ σ₂}
    → Exec s σ σ₁
    → Exec s σ σ₂
    → σ₁ ≡ σ₂
  exec-deterministic = WhileSem.exec-deterministic
