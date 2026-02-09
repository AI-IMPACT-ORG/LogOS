{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Backend where

open import LogOS.Prelude

open import LogOS.UniversalIR.Core
open import LogOS.UniversalIR.IR using (lowerToIR; decode)

-- A backend provides a compiler into a brand-specific code carrier and an
-- injection into the shared IR carrier `UCode`. Lowering to the canonical IR
-- branch is uniform (`lowerToIR`).
--
-- Note: this module exposes a step-budgeted `exec`/`decodeAt` convenience API.
-- The scheme-centric semantics (“machines as schemes”, fuel-free normalisation,
-- observational equality) lives in `LogOS.Computation.Scheme` and
-- `LogOS.UniversalIR.Schemes`.

record Backend {ℓI ℓB : Level} (Input : Set ℓI) (BrandCode : Set ℓB)
  : Set (lsuc (ℓI ⊔ ℓB)) where
  constructor mkBackend
  field
    compile : Input → BrandCode
    inject  : BrandCode → UCode

  toUCode : Input → UCode
  toUCode x = inject (compile x)

  exec : ℕ → Input → UCode
  exec fuel x = simulate fuel (toUCode x)

  toIRAt : ℕ → Input → UCode
  toIRAt fuel x = lowerToIR (exec fuel x)

  decodeAt : ℕ → Input → ℕ
  decodeAt fuel x = decode (toIRAt fuel x)
