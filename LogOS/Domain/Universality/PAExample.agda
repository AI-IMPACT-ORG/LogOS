{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.PAExample where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)

open import LogOS.Domain.Universality.Core

-- One PA computation across all schemes: “decrement-to-zero” in n steps.
-- We encode an input n the same way in each branch and show simulateToy n reaches
-- the expected halted configuration.

encodeT : ℕ → ToyUCode
encodeT n = ToyT (mkT 0 n)

encodeC : ℕ → ToyUCode
encodeC n = ToyC (mkC n)

encodeQ : ℕ → ToyUCode
encodeQ n = ToyQ (mkToyQ n)

encodeB : ℕ → ToyUCode
encodeB n = ToyB (mkB 0 n)

-- Sample equalities (executable): same input n represented in each scheme.

exT2 : simulateToy 2 (encodeT 2) ≡ ToyT (mkT 2 0)
exT2 = refl

exC2 : simulateToy 2 (encodeC 2) ≡ ToyC (mkC 0)
exC2 = refl

exQ2 : simulateToy 2 (encodeQ 2) ≡ ToyQ (mkToyQ 0)
exQ2 = refl

exB2 : simulateToy 2 (encodeB 2) ≡ ToyB (mkB 2 0)
exB2 = refl

exT3 : simulateToy 3 (encodeT 3) ≡ ToyT (mkT 3 0)
exT3 = refl

exC3 : simulateToy 3 (encodeC 3) ≡ ToyC (mkC 0)
exC3 = refl

exQ3 : simulateToy 3 (encodeQ 3) ≡ ToyQ (mkToyQ 0)
exQ3 = refl

exB3 : simulateToy 3 (encodeB 3) ≡ ToyB (mkB 3 0)
exB3 = refl
