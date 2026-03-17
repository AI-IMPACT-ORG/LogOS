{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.Witness where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; just
  )

open import LogOS.Apps.ZFC.Metamath.BiDirectional.Reify using (toPFormula)
open import LogOS.Apps.ZFC.Metamath.BiDirectional.Rename using (renameFormulaByEnv)
open import LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip using (toFormulaRenamingRoundTrip)

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using
  ( PFormula
  ; toFormula
  )

open import LogOS.Apps.ZFC.Proof.Syntax using (Formula)

-- Bidirectional witness: a successful encoding certificate for one formula,
-- together with the explicit renaming witness used by decoding.
--
-- Think of this as the concrete "birepresentation" object for a particular
-- environment and formula:
--   - `pFormula` is the encoded PFormula
--   - `encodeRoundTrip` is the forward direction
--   - `decodeRoundTrip` is the backward direction up to the required
--     environment-threaded renaming
record BidirWitness (env : List ℕ) (φ : Formula) : Set where
  constructor mkBidirWitness
  field
    pFormula : PFormula
    encodeRoundTrip : toPFormula env φ ≡ just pFormula
    decodeRoundTrip : toFormula pFormula ≡ just (renameFormulaByEnv env φ)

mkBidirWitnessFromEncode
  : ∀ env φ p
    → toPFormula env φ ≡ just p
    → BidirWitness env φ
mkBidirWitnessFromEncode env φ p hP =
  mkBidirWitness p hP (toFormulaRenamingRoundTrip env φ p hP)
