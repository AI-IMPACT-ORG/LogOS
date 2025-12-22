{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.IR where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Encoding public using (take; double; bitsToNat)

open import Data.List using (List; []; _∷_)

-- Canonical lowering: map any brand-specific UCode variant to the universal IR
-- (the lambda/Church-numeral branch), extracting an "answer" from each brand.
lowerToIR : UCode → UCode
lowerToIR (UM m) = UL (mkL (church (MinskyCode.r0 m)))
lowerToIR (UL l) = UL l
lowerToIR (UE e) with EVMCode.stack e
... | []       = UL (mkL (church 0))
... | (x ∷ _)  = UL (mkL (church x))
lowerToIR (UQ q) = UL (mkL (church (QuantumCode.r0 q)))
lowerToIR (UQC q) = UL (mkL (church (bitsToNat (take (QuantumCircuitCode.outLen q) (QuantumCircuitCode.wires q)))))

-- Canonical decoding of answers from the universal IR.
-- In this library, the IR is chosen so that answers live in the `UL` branch
-- as Church numerals.
decode : UCode → ℕ
decode (UL l) = decodeChurch (LambdaCode.term l)
decode (UM _) = 0
decode (UE _) = 0
decode (UQ _) = 0
decode (UQC _) = 0

-- Semantic center (Plan B): canonical observation on the universal carrier.
-- This is the single “meaning extractor” used throughout the UniversalIR view.

observe : UCode → ℕ
observe u = decode (lowerToIR u)

-- `lowerToIR` is a (lax) normaliser into the chosen canonical branch.
-- In particular, it is idempotent.

lowerToIR-idem : ∀ u → lowerToIR (lowerToIR u) ≡ lowerToIR u
lowerToIR-idem (UM _) = refl
lowerToIR-idem (UL _) = refl
lowerToIR-idem (UE e) with EVMCode.stack e
... | []      = refl
... | (_ ∷ _) = refl
lowerToIR-idem (UQ _) = refl
lowerToIR-idem (UQC _) = refl
