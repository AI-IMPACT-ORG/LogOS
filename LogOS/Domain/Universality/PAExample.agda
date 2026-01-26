{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.PAExample where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ; zero; suc)

open import LogOS.Domain.Universality.Core

-- One PA computation across all schemes: “decrement-to-zero” in n steps.
-- We encode an input n the same way in each branch and show simulateCoreU n reaches
-- the expected halted configuration.

encodeT : ℕ → CoreUCode
encodeT n = CoreT (mkT 0 n)

encodeC : ℕ → CoreUCode
encodeC n = CoreC (mkC n)

encodeQ : ℕ → CoreUCode
encodeQ n = CoreQ (mkCoreQ n)

encodeB : ℕ → CoreUCode
encodeB n = CoreB (mkB 0 n)

-- Sample equalities (executable): same input n represented in each scheme.

exT2 : simulateCoreU 2 (encodeT 2) ≡ CoreT (mkT 2 0)
exT2 = refl

exC2 : simulateCoreU 2 (encodeC 2) ≡ CoreC (mkC 0)
exC2 = refl

exQ2 : simulateCoreU 2 (encodeQ 2) ≡ CoreQ (mkCoreQAt 2 2)
exQ2 = refl

exB2 : simulateCoreU 2 (encodeB 2) ≡ CoreB (mkB 2 0)
exB2 = refl

exT3 : simulateCoreU 3 (encodeT 3) ≡ CoreT (mkT 3 0)
exT3 = refl

exC3 : simulateCoreU 3 (encodeC 3) ≡ CoreC (mkC 0)
exC3 = refl

exQ3 : simulateCoreU 3 (encodeQ 3) ≡ CoreQ (mkCoreQAt 3 3)
exQ3 = refl

exB3 : simulateCoreU 3 (encodeB 3) ≡ CoreB (mkB 3 0)
exB3 = refl
