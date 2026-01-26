{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.SmallStep where

open import LogOS.Prelude

open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.Product using (Σ; _,_; _×_)

open import LogOS.Domain.UniversalIR.While.Language
open import LogOS.Domain.UniversalIR.While.Semantics
open import LogOS.Domain.UniversalIR.While.Typing

-- Small-step semantics for the While fragment.

inspect : ∀ {A : Set} (x : A) → Σ A (λ y → x ≡ y)
inspect x = x , refl

data Step : Stmt → Store → Stmt → Store → Set where
  step-inc :
    ∀ {v σ} →
    Step (inc v) σ skip (stepInc v σ)

  step-dec :
    ∀ {v σ} →
    Step (dec v) σ skip (stepDec v σ)

  step-mulAB :
    ∀ {σ} →
    Step mulAB σ skip (stepMulAB σ)

  step-seq-step :
    ∀ {s t σ σ' s'} →
    Step s σ s' σ' →
    Step (s >> t) σ (s' >> t) σ'

  step-seq-done :
    ∀ {t σ} →
    Step (skip >> t) σ t σ

  step-while-zero :
    ∀ {v body σ} →
    get v σ ≡ 0 →
    Step (whileNZ v body) σ skip σ

  step-while-step :
    ∀ {v body σ n} →
    get v σ ≡ suc n →
    Step (whileNZ v body) σ (body >> whileNZ v body) σ

-- Multi-step closure (small-step reachability).

data Steps : Stmt → Store → Stmt → Store → Set where
  steps-refl :
    ∀ {s σ} →
    Steps s σ s σ

  steps-step :
    ∀ {s σ s' σ' s'' σ''} →
    Step s σ s' σ' →
    Steps s' σ' s'' σ'' →
    Steps s σ s'' σ''

steps-trans
  : ∀ {s σ s' σ' s'' σ''}
  → Steps s σ s' σ'
  → Steps s' σ' s'' σ''
  → Steps s σ s'' σ''
steps-trans steps-refl steps₂ = steps₂
steps-trans (steps-step step₁ rest₁) steps₂ =
  steps-step step₁ (steps-trans rest₁ steps₂)

steps-seq-left
  : ∀ {s t σ s' σ'}
  → Steps s σ s' σ'
  → Steps (s >> t) σ (s' >> t) σ'
steps-seq-left steps-refl = steps-refl
steps-seq-left (steps-step stepS rest) =
  steps-step (step-seq-step stepS) (steps-seq-left rest)

exec→steps
  : ∀ {s σ σ'}
  → Exec s σ σ'
  → Steps s σ skip σ'
exec→steps exec-skip = steps-refl
exec→steps exec-inc = steps-step step-inc steps-refl
exec→steps exec-dec = steps-step step-dec steps-refl
exec→steps exec-mulAB = steps-step step-mulAB steps-refl
exec→steps (exec-seq execS execT) =
  let
    stepsS = exec→steps execS
    stepsT = exec→steps execT
    toSkipT = steps-step step-seq-done stepsT
  in
  steps-trans (steps-seq-left stepsS) toSkipT
exec→steps (exec-while-zero eq) = steps-step (step-while-zero eq) steps-refl
exec→steps (exec-while-step eq execBody execLoop) =
  let
    stepsBody = exec→steps execBody
    stepsLoop = exec→steps execLoop
    bodyToLoop =
      steps-trans
        (steps-seq-left stepsBody)
        (steps-step step-seq-done stepsLoop)
  in
  steps-step (step-while-step eq) bodyToLoop

step→exec
  : ∀ {s σ s' σ' σ''}
  → Step s σ s' σ'
  → Exec s' σ' σ''
  → Exec s σ σ''
step→exec step-inc exec-skip = exec-inc
step→exec step-dec exec-skip = exec-dec
step→exec step-mulAB exec-skip = exec-mulAB
step→exec (step-seq-step stepS) (exec-seq execS execT) =
  exec-seq (step→exec stepS execS) execT
step→exec step-seq-done execT =
  exec-seq exec-skip execT
step→exec (step-while-zero eq) exec-skip = exec-while-zero eq
step→exec (step-while-step eq) (exec-seq execBody execLoop) =
  exec-while-step eq execBody execLoop

steps→exec
  : ∀ {s σ σ'}
  → Steps s σ skip σ'
  → Exec s σ σ'
steps→exec steps-refl = exec-skip
steps→exec (steps-step stepS rest) = step→exec stepS (steps→exec rest)

-- Progress: a well-typed statement can always step, unless it is already skip.

progress-eff
  : ∀ {s σ e}
  → StmtEff s e
  → (s ≡ skip) ⊎ Σ Stmt (λ s' → Σ Store (λ σ' → Step s σ s' σ'))
progress-eff {σ = σ} eff-skip = inj₁ refl
progress-eff {σ = σ} (eff-inc {v}) = inj₂ (skip , (stepInc v σ , step-inc))
progress-eff {σ = σ} (eff-dec {v}) = inj₂ (skip , (stepDec v σ , step-dec))
progress-eff {σ = σ} eff-mulAB = inj₂ (skip , (stepMulAB σ , step-mulAB))
progress-eff {σ = σ} (eff-seq {s = s₁} {t = t} effS effT) with progress-eff effS
... | inj₁ s≡skip =
  inj₂
    ( t
    , (σ , subst (λ s' → Step (s' >> t) σ t σ) (sym s≡skip) step-seq-done)
    )
... | inj₂ (s' , σ' , stepS) =
  inj₂ ((s' >> t) , (σ' , step-seq-step stepS))
progress-eff {σ = σ} (eff-while {v} {body} effBody) with inspect (get v σ)
... | zero , eq =
  inj₂ (skip , (σ , step-while-zero eq))
... | suc n , eq =
  inj₂ ((body >> whileNZ v body) , (σ , step-while-step eq))

progress
  : ∀ {s σ}
  → StmtOk s
  → (s ≡ skip) ⊎ Σ Stmt (λ s' → Σ Store (λ σ' → Step s σ s' σ'))
progress = progress-eff

-- Preservation: residual effect is bounded by the original effect.
preservation-eff
  : ∀ {s σ s' σ' e}
  → StmtEff s e
  → Step s σ s' σ'
  → Σ Eff (λ e' → StmtEff s' e' × e' ≤eff e)
preservation-eff eff-skip ()
preservation-eff (eff-inc {v}) step-inc =
  effNone , (eff-skip , effLe-bottom _)
preservation-eff (eff-dec {v}) step-dec =
  effNone , (eff-skip , effLe-bottom _)
preservation-eff eff-mulAB step-mulAB =
  effNone , (eff-skip , effLe-bottom _)
preservation-eff (eff-seq {e₂ = e₂} effS effT) (step-seq-step stepS) =
  let
    e' , (effS' , le) = preservation-eff effS stepS
    effS'T = eff-seq effS' effT
  in
  (effJoin e' e₂ , (effS'T , effJoin-mono-left le))
preservation-eff (eff-seq {e₂ = e₂} eff-skip effT) step-seq-done =
  e₂ , (effT , effJoin-upper-right effNone e₂)
preservation-eff (eff-while effBody) (step-while-zero _) =
  effNone , (eff-skip , effLe-bottom _)
preservation-eff (eff-while {v = v} {body = body} {e = e} effBody) (step-while-step _) =
  let
    effLoop = eff-seq effBody (eff-while effBody)
    absorb = effJoin-absorb-left e (effGuard v)
  in
  effJoin (effGuard v) e
    , ( subst (λ e' → StmtEff (body >> whileNZ v body) e') absorb effLoop
      , effLe-refl (effJoin (effGuard v) e)
      )

-- Named alias to emphasize the "bounded effect" preservation.
preservation-bounded
  : ∀ {s σ s' σ' e}
  → StmtEff s e
  → Step s σ s' σ'
  → Σ Eff (λ e' → StmtEff s' e' × e' ≤eff e)
preservation-bounded = preservation-eff

preservation
  : ∀ {s σ s' σ' e}
  → StmtEff s e
  → Step s σ s' σ'
  → Σ Eff (λ e' → StmtEff s' e' × e' ≤eff e)
preservation = preservation-bounded

preservation-ok
  : ∀ {s σ s' σ'}
  → StmtOk s
  → Step s σ s' σ'
  → StmtOk s'
preservation-ok {s' = s'} effS stepS =
  let
    e' , (effS' , _) = preservation-bounded effS stepS
  in
  subst (StmtEff s') (sym (stmtEff-sound effS')) effS'

-- Determinism: small-step semantics is functional.

deterministic
  : ∀ {s σ s₁ σ₁ s₂ σ₂}
  → Step s σ s₁ σ₁
  → Step s σ s₂ σ₂
  → s₁ ≡ s₂ × σ₁ ≡ σ₂
deterministic step-inc step-inc = (refl , refl)
deterministic step-dec step-dec = (refl , refl)
deterministic step-mulAB step-mulAB = (refl , refl)
deterministic (step-seq-step {t = t} step₁) (step-seq-step step₂) =
  let
    (eqS , eqσ) = deterministic step₁ step₂
  in
  (cong (λ s' → s' >> t) eqS , eqσ)
deterministic (step-seq-step step₁) step-seq-done with step₁
... | ()
deterministic step-seq-done (step-seq-step step₂) with step₂
... | ()
deterministic step-seq-done step-seq-done = (refl , refl)
deterministic (step-while-zero eq₀) (step-while-zero _) = (refl , refl)
deterministic (step-while-zero eq₀) (step-while-step eq₁) with trans (sym eq₀) eq₁
... | ()
deterministic (step-while-step eq₁) (step-while-zero eq₀) with trans (sym eq₀) eq₁
... | ()
deterministic (step-while-step _) (step-while-step _) = (refl , refl)
