{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Interpretation.DB where

-- Convenience: interpret directly from a Metamath-style DB port.
--
-- This layer consumes a DB through the same closure + normalization pipeline
-- used by the bidirectional emission tests; it is not itself an exact
-- syntactic inverse of `BiDirectional.mkTokenDB`.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Ports.Metamath as MM using (Database)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  ; mapMaybe
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using (Sig)
open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using (PFormula)
open import LogOS.Apps.ZFC.Proof.Syntax using (Formula)

open import LogOS.Apps.ZFC.Metamath.Interpretation.Pipeline using
  ( ConclPipeline
  ; ConclPipelineWithRest
  ; parseClosedConcl
  ; parseClosedConclWithEnvBulk
  ; parsedConcl
  )

open import LogOS.Apps.ZFC.Metamath.Interpretation.Interpret using
  ( interpretMetaFree )

record SetMMZFLedger {ℓ : Level} (Label : Set ℓ) : Set (lsuc ℓ) where
  field
    axExtensionality : Label
    axEmpty          : Label
    axPairing        : Label
    axUnion          : Label
    axPowerset       : Label
    axInfinity       : Label
    axFoundation     : Label
    axSeparation     : Label
    axReplacement    : Label

open SetMMZFLedger public

module ForDB
  (S  : Sig)
  (DB : Database (List ℕ))
  where
  open MM.Database DB

  parseConcl : Label → Maybe ConclPipeline
  parseConcl l = parseClosedConcl S (hyps l) (concl l)

  parseConclWithRest : Label → Maybe ConclPipelineWithRest
  parseConclWithRest l = parseClosedConclWithEnvBulk S (hyps l) [] (concl l)

  interpretConcl : Label → Maybe Formula
  interpretConcl l = parseConcl l >>= interpretMetaFree

  -- Bulk helpers for the ZF/ZFC axiom labels (no global choice).
  --
  -- This is intentionally “ledger-shaped”: the caller chooses which DB labels
  -- correspond to the intended axiom roles (e.g. `ax-ext`, `ax-sep`, ... in Set.MM).

  record ParsedAxioms : Set where
    field
      extensionality : Maybe PFormula
      empty          : Maybe PFormula
      pairing        : Maybe PFormula
      union          : Maybe PFormula
      powerset       : Maybe PFormula
      infinity       : Maybe PFormula
      foundation     : Maybe PFormula
      separation     : Maybe PFormula
      replacement    : Maybe PFormula

  record InterpretedAxioms : Set where
    field
      extensionality : Maybe Formula
      empty          : Maybe Formula
      pairing        : Maybe Formula
      union          : Maybe Formula
      powerset       : Maybe Formula
      infinity       : Maybe Formula
      foundation     : Maybe Formula
      separation     : Maybe Formula
      replacement    : Maybe Formula

  parseLedger : SetMMZFLedger Label → ParsedAxioms
  parseLedger L =
    record
      { extensionality = mapMaybe parsedConcl (parseConcl (axExtensionality L))
      ; empty          = mapMaybe parsedConcl (parseConcl (axEmpty L))
      ; pairing        = mapMaybe parsedConcl (parseConcl (axPairing L))
      ; union          = mapMaybe parsedConcl (parseConcl (axUnion L))
      ; powerset       = mapMaybe parsedConcl (parseConcl (axPowerset L))
      ; infinity       = mapMaybe parsedConcl (parseConcl (axInfinity L))
      ; foundation     = mapMaybe parsedConcl (parseConcl (axFoundation L))
      ; separation     = mapMaybe parsedConcl (parseConcl (axSeparation L))
      ; replacement    = mapMaybe parsedConcl (parseConcl (axReplacement L))
      }

  interpretLedger : SetMMZFLedger Label → InterpretedAxioms
  interpretLedger L =
    record
      { extensionality = interpretConcl (axExtensionality L)
      ; empty          = interpretConcl (axEmpty L)
      ; pairing        = interpretConcl (axPairing L)
      ; union          = interpretConcl (axUnion L)
      ; powerset       = interpretConcl (axPowerset L)
      ; infinity       = interpretConcl (axInfinity L)
      ; foundation     = interpretConcl (axFoundation L)
      ; separation     = interpretConcl (axSeparation L)
      ; replacement    = interpretConcl (axReplacement L)
      }
