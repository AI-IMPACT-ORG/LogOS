{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.SchemePresentation where

-- A Scheme presentation for the universality core.
-- The input explicitly carries a fuel bound, so `run` coincides with `simulateCoreU`.

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)

open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Minimal.Closure using (ClosureOp)
open import LogOS.Minimal.Adapter using (QAdapter; trivialQAdapter)
import LogOS.Computation.Scheme as Scheme

open import LogOS.Domain.Universality.Core using (CoreUCode; stepCoreU; simulateCoreU)

record CoreInput : Set where
  constructor mkInput
  field
    fuel : ℕ
    code : CoreUCode

open CoreInput public

coreCP : ConPoset lzero
coreCP =
  record
    { Con  = CoreUCode
    ; _⊑_  = _≡_
    ; refl = refl
    ; trans = λ {a} {b} {c} → trans
    }

coreClosure : ClosureOp coreCP
coreClosure =
  record
    { cl        = λ c → c
    ; mono      = λ {c} {d} eq → eq
    ; infl      = λ _ → refl
    ; idemp-lax = λ _ → refl
    }

CoreScheme : Scheme.Scheme {ℓI = lzero} {ℓO = lzero} {ℓC = lzero} {ℓQ = lzero} CoreInput CoreUCode
CoreScheme =
  record
    { CP       = coreCP
    ; Step     = stepCoreU
    ; Norm     = coreClosure
    ; compile  = code
    ; fuel     = fuel
    ; decode   = λ x → x
    ; Q        = trivialQAdapter
    ; stepCost = λ _ → QAdapter.e trivialQAdapter
    }

exec-simulate
  : ∀ n u → Scheme.exec CoreScheme n (mkInput n u) ≡ simulateCoreU n u
exec-simulate zero u = refl
exec-simulate (suc n) u = exec-simulate n (stepCoreU u)

run-simulate
  : ∀ n u → Scheme.run CoreScheme (mkInput n u) ≡ simulateCoreU n u
run-simulate n u = exec-simulate n u
