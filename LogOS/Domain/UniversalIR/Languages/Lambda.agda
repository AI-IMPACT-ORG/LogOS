{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Languages.Lambda where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Task using (PATask; Add; Mul; eval)
open import LogOS.Domain.UniversalIR.Backend using (Backend; mkBackend)
open import LogOS.Domain.UniversalIR.Core

-- Lambda backend (untyped, Church numeral output).
--
-- This file provides a simple step-budget wrapper (`fuel`, `run`) for convenience.
-- The canonical universality story compares backends as `Scheme` choices; see
-- `LogOS.Domain.UniversalIR.Schemes`.
-- We define the usual Church-encoded λ-terms for addition/multiplication:
--   plus m n = λf.λx. m f (n f x)

plus : Term
plus =
  lam (lam (lam (lam
    (app (app (var 3) (var 1))
         (app (app (var 2) (var 1)) (var 0))))))

mult : Term
mult =
  lam (lam (lam (lam
    (app (app (var 3) (app (var 2) (var 1)))
         (var 0)))))

-- Raw lambda compilation (beta-reduction route).
compileRawBrand : PATask → LambdaCode
compileRawBrand t with PATask.op t
... | Add = mkL (app (app plus (church (PATask.a t))) (church (PATask.b t)))
... | Mul = mkL (app (app mult (church (PATask.a t))) (church (PATask.b t)))

-- Certified compilation: emit the canonical Church numeral of `eval`.
-- (Use `compileRawBrand` if you want the explicit β-reduction path.)
compileBrand : PATask → LambdaCode
compileBrand t = mkL (church (eval t))

backend : Backend PATask LambdaCode
backend = mkBackend compileBrand UL

compile : PATask → UCode
compile t = Backend.toUCode backend t

-- The term is already in normal form, so any fuel works; keep a coarse bound.
fuel : PATask → ℕ
fuel t with PATask.op t
... | Add = ((PATask.a t) + (PATask.b t)) + 200
... | Mul = ((PATask.a t) * (PATask.b t)) + 400

exec : ℕ → PATask → UCode
exec n t = Backend.exec backend n t

toIR : PATask → UCode
toIR t = Backend.toIRAt backend (fuel t) t

run : PATask → ℕ
run t = Backend.decodeAt backend (fuel t) t
