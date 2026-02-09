{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Futamura where

-- Futamura (conservative, scheme-level form) for the UniversalIR semantic center.
--
-- This module does *not* assume a code-level partial evaluator or quoting. It
-- expresses the first Futamura projection as the universal “staging” operation
-- on scheme interfaces:
--
--   specialise : Interface (Static × Dynamic) P → Static → Interface Dynamic P
--
-- Instantiated to the UniversalIR semantic center (`UProcess`), the “interpreter”
-- takes a pair (program , fuel) and returns its observation after `fuel` steps.
-- Specialising by a program yields a residual scheme that runs that fixed
-- program, parameterised only by the fuel.

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; []; _∷_)

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Computation.Core using (iterate)

open import LogOS.UniversalIR.Core using (UCode; UM; UL; UE; UQ; UQC; stepU; simulate)
import LogOS.UniversalIR.Core.Minsky as M
import LogOS.UniversalIR.Core.Lambda as L
import LogOS.UniversalIR.Core.Ethereum as E
import LogOS.UniversalIR.Core.QuantumOracle as QO
import LogOS.UniversalIR.Core.QuantumCircuit as QC
open import LogOS.UniversalIR.IR using (observe)
open import LogOS.UniversalIR.Schemes using (UProcess)

-- Universal evaluator interface: “run this `UCode` for `n` steps”.
--
-- We keep fuel explicit in the input type, so staging can curry on the program.

EvalI : Cat.Interface (UCode × ℕ) UProcess
EvalI =
  record
    { compile = fst
    ; fuel    = snd
    }

EvalS : Sch.Scheme (UCode × ℕ) ℕ
EvalS = Cat.schemeFromInterface UProcess EvalI

-- First Futamura projection (scheme-level): specialise the evaluator by fixing
-- the program.

RunI : UCode → Cat.Interface ℕ UProcess
RunI u = Cat.specializeInterface EvalI u

RunS : UCode → Sch.Scheme ℕ ℕ
RunS u = Cat.schemeFromInterface UProcess (RunI u)

-- Correctness (pure currying): specialising by `u` commutes with `run`.

futamura₁-run
  : ∀ u n
  → Sch.run (RunS u) n ≡ Sch.run EvalS (u , n)
futamura₁-run u n = Cat.run-specializeInterface EvalI u n

-- Concrete reading: `RunS u` computes `observe (simulate n u)`.
--
-- This is definitional in the UniversalIR setup (UProcess uses `stepU` and
-- `observe`), so the proof is `refl`.

run≡observe-simulate
  : ∀ u n
  → Sch.run (RunS u) n ≡ observe (simulate n u)
run≡observe-simulate u n =
  cong observe (iterate≡simulate n u)
  where
    iterate≡simulate
      : ∀ n u
      → iterate (Sch.Scheme.Comp (RunS u)) n u ≡ simulate n u
    iterate≡simulate zero    _ = refl
    iterate≡simulate (suc n) u = iterate≡simulate n (stepU u)

-- ============================================================================
-- Stronger Futamura-1 (program-level, for split-code branches)
--
-- When a branch admits a program/state split, we can stage the evaluator by the
-- *program only*, leaving the initial machine state as dynamic input. This is a
-- non-degenerate “residualization” step inside UniversalIR: the residual scheme
-- depends only on a program, and can be run on many different inputs (states).
-- ============================================================================

module Split
  {Prog State Code : Set}
  (inject : Code → UCode)
  (mk : State → Prog → Code)
  where

  EvalIᵖ : Cat.Interface (Prog × (State × ℕ)) UProcess
  EvalIᵖ =
    record
      { compile = λ (p , (st , _)) → inject (mk st p)
      ; fuel    = λ (_ , (_ , n)) → n
      }

  EvalSᵖ : Sch.Scheme (Prog × (State × ℕ)) ℕ
  EvalSᵖ = Cat.schemeFromInterface UProcess EvalIᵖ

  RunIᵖ : Prog → Cat.Interface (State × ℕ) UProcess
  RunIᵖ p = Cat.specializeInterface EvalIᵖ p

  RunSᵖ : Prog → Sch.Scheme (State × ℕ) ℕ
  RunSᵖ p = Cat.schemeFromInterface UProcess (RunIᵖ p)

  futamura₁-runᵖ
    : ∀ p st n
    → Sch.run (RunSᵖ p) (st , n) ≡ Sch.run EvalSᵖ (p , (st , n))
  futamura₁-runᵖ p st n =
    Cat.run-specializeInterface EvalIᵖ p (st , n)

  run≡observe-simulateᵖ
    : ∀ p st n
    → Sch.run (RunSᵖ p) (st , n)
        ≡ observe (simulate n (inject (mk st p)))
  run≡observe-simulateᵖ p st n =
    cong observe (iterate≡simulate n (inject (mk st p)))
    where
      iterate≡simulate
        : ∀ n u
        → iterate (Sch.Scheme.Comp (RunSᵖ p)) n u ≡ simulate n u
      iterate≡simulate zero    _ = refl
      iterate≡simulate (suc n) u = iterate≡simulate n (stepU u)

module Minsky where
  open Split UM M.mkCode public
    renaming
      ( EvalIᵖ to EvalI
      ; EvalSᵖ to EvalS
      ; RunIᵖ  to RunI
      ; RunSᵖ  to RunS
      ; futamura₁-runᵖ to futamura₁-run
      ; run≡observe-simulateᵖ to run≡observe-simulate
      )

-- Lambda (term-normalisation) is special: the code carrier is a term, so it
-- does not admit a machine-like “program invariant under stepping” split.
--
-- To align with the standard Futamura setup (“interpreter over program×data”),
-- we treat:
-- - `Prog`  as a λ-term (the program), and
-- - `State` as a list of λ-terms (dynamic inputs / arguments),
-- and build the initial configuration by iterated application.
--
-- This makes “stage by program only” non-degenerate for λ-calculus, without
-- changing the canonical IR branch (`UL`).
module Lambda where
  open L using (Term; LambdaCode; mkL; app)

  applyArgs : Term → List Term → Term
  applyArgs t [] = t
  applyArgs t (u ∷ us) = applyArgs (app t u) us

  mkCode : List Term → Term → LambdaCode
  mkCode args p = mkL (applyArgs p args)

  open Split UL mkCode public
    renaming
      ( EvalIᵖ to EvalI
      ; EvalSᵖ to EvalS
      ; RunIᵖ  to RunI
      ; RunSᵖ  to RunS
      ; futamura₁-runᵖ to futamura₁-run
      ; run≡observe-simulateᵖ to run≡observe-simulate
      )

module Ethereum where
  open Split UE E.mkCode public
    renaming
      ( EvalIᵖ to EvalI
      ; EvalSᵖ to EvalS
      ; RunIᵖ  to RunI
      ; RunSᵖ  to RunS
      ; futamura₁-runᵖ to futamura₁-run
      ; run≡observe-simulateᵖ to run≡observe-simulate
      )

module QuantumOracle where
  open Split UQ QO.mkCode public
    renaming
      ( EvalIᵖ to EvalI
      ; EvalSᵖ to EvalS
      ; RunIᵖ  to RunI
      ; RunSᵖ  to RunS
      ; futamura₁-runᵖ to futamura₁-run
      ; run≡observe-simulateᵖ to run≡observe-simulate
      )

module QuantumCircuit where
  open Split UQC QC.mkCode public
    renaming
      ( EvalIᵖ to EvalI
      ; EvalSᵖ to EvalS
      ; RunIᵖ  to RunI
      ; RunSᵖ  to RunS
      ; futamura₁-runᵖ to futamura₁-run
      ; run≡observe-simulateᵖ to run≡observe-simulate
      )

-- ============================================================================
-- Classical (code-producing) Futamura projections (assumption-scoped)
--
-- The sections above are the *scheme-level* (semantic) Futamura story: staging
-- is just currying an interface, and it is mechanised for the UniversalIR
-- semantic center. This already yields a meaningful “projection 1” inside LogOS
-- without assuming quotation or a reflective compiler.
--
-- The textbook “Futamura 2/3” story is about *code-producing* partial
-- evaluators and self-application. UniversalIR does not currently internalise a
-- quoting/reflective layer for `UCode`, so we expose the classical story as an
-- explicit interface of assumptions. Any future reflective instantiation should
-- do so by providing a `CodeFutamura` instance.
-- ============================================================================

record CodeFutamura {ℓ : Level} (Code : Set ℓ) : Set (lsuc ℓ) where
  field
    pair : Code → Code → Code
    eval : Code → Code → Code
    mix  : Code

    -- Correctness for the *mix* program:
    --
    -- `eval mix (pair int p)` produces residual code specialised by the static
    -- input `p`. Running that residual code on dynamic input `d` agrees with
    -- running the interpreter `int` on the paired input `(p , d)`.
    futamura₁
      : ∀ int p d
      → eval (eval mix (pair int p)) d ≡ eval int (pair p d)

  -- Derived objects ----------------------------------------------------------

  compile₁ : Code → Code → Code
  compile₁ int p = eval mix (pair int p)

  compiler₂ : Code → Code
  compiler₂ int = eval mix (pair mix int)

  cogen₃ : Code
  cogen₃ = eval mix (pair mix mix)

  -- Derived projections ------------------------------------------------------

  futamura₁'
    : ∀ int p d
    → eval (compile₁ int p) d ≡ eval int (pair p d)
  futamura₁' int p d = futamura₁ int p d

  futamura₂
    : ∀ int p
    → eval (compiler₂ int) p ≡ compile₁ int p
  futamura₂ int p = futamura₁ mix int p

  futamura₂'
    : ∀ int p d
    → eval (eval (compiler₂ int) p) d ≡ eval int (pair p d)
  futamura₂' int p d =
    trans
      (cong (λ c → eval c d) (futamura₂ int p))
      (futamura₁' int p d)

  futamura₃
    : ∀ int
    → eval cogen₃ int ≡ compiler₂ int
  futamura₃ int = futamura₁ mix mix int

  futamura₃'
    : ∀ int p
    → eval (eval cogen₃ int) p ≡ compile₁ int p
  futamura₃' int p =
    trans
      (cong (λ c → eval c p) (futamura₃ int))
      (futamura₂ int p)
