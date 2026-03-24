{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Irreversibility.MeasurementCoarseGrainCompression where

-- Coarse-graining example over the measurement boundary:
-- `{fine, coarse}` collapses to `{coarse}` without appealing to partiality.

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
open import LogOS.Prelude.Fin using (fzero; fsuc; _≢_)
open import LogOS.Prelude.FiniteFamily using (FiniteFamily)
open import LogOS.LT.ConPreorder using (_≈_; ≈-sym)
open import LogOS.LT.View using (View; idView; pullbackView)
open import LogOS.LT.View.Factorisation using (FactorisesThrough; mapFactorisation)
open import LogOS.Ports.Opacity.Distinguishability using
  ( DistinguishableFamily
  ; family
  )
open import LogOS.Ports.Opacity.FiniteCompression using (FiniteCompressionWitness)

import LogOS.Apps.Physics.MeasurementExample as Measurement

coarseGrainMap : Measurement.Outcome → Measurement.Outcome
coarseGrainMap Measurement.coarse = Measurement.coarse
coarseGrainMap Measurement.fine = Measurement.coarse

coarseGrainMono
  : LogOS.LT.ConPreorder.MonoMap
      Measurement.OutcomePreorder
      Measurement.OutcomePreorder
      coarseGrainMap
coarseGrainMono {Measurement.coarse} {Measurement.coarse} tt = tt
coarseGrainMono {Measurement.coarse} {Measurement.fine} tt = tt
coarseGrainMono {Measurement.fine} {Measurement.fine} tt = tt

privateView : View Measurement.Outcome Measurement.OutcomePreorder
privateView = idView Measurement.OutcomePreorder

publicView : View Measurement.Outcome Measurement.OutcomePreorder
publicView = pullbackView coarseGrainMap (idView Measurement.OutcomePreorder)

coarseGrainFactorisation : FactorisesThrough privateView publicView
coarseGrainFactorisation =
  mapFactorisation coarseGrainMap coarseGrainMono

rawSourceFamily : FiniteFamily Measurement.Outcome
rawSourceFamily =
  record
    { size = suc (suc zero)
    ; at = λ where
        fzero → Measurement.coarse
        (fsuc fzero) → Measurement.fine
    }

sourceFamily : DistinguishableFamily privateView
sourceFamily =
  record
    { family = rawSourceFamily
    ; separated = sourceSeparated
    }
  where
    fine≉coarse : ¬ _≈_ Measurement.OutcomePreorder Measurement.fine Measurement.coarse
    fine≉coarse eq = Measurement.not-fine-refines-coarse (fst eq)

    coarse≉fine : ¬ _≈_ Measurement.OutcomePreorder Measurement.coarse Measurement.fine
    coarse≉fine eq = fine≉coarse (≈-sym {CP = Measurement.OutcomePreorder} eq)

    sourceSeparated : ∀ i j → i ≢ j → ¬ _≈_ Measurement.OutcomePreorder
      (FiniteFamily.at rawSourceFamily i)
      (FiniteFamily.at rawSourceFamily j)
    sourceSeparated fzero fzero neq _ = neq refl
    sourceSeparated fzero (fsuc fzero) neq = coarse≉fine
    sourceSeparated (fsuc fzero) fzero neq = fine≉coarse
    sourceSeparated (fsuc fzero) (fsuc fzero) neq _ = neq refl

targetFamily : DistinguishableFamily publicView
targetFamily =
  record
    { family =
        record
          { size = suc zero
          ; at = λ { fzero → Measurement.coarse }
          }
    ; separated = λ where
        fzero fzero neq _ → neq refl
    }

measurementFiniteCompression : FiniteCompressionWitness coarseGrainFactorisation
measurementFiniteCompression =
  record
    { source = sourceFamily
    ; target = targetFamily
    ; assign = λ _ → fzero
    ; sound = λ where
        fzero → (tt , tt)
        (fsuc fzero) → (tt , tt)
    ; surjective = λ { fzero → fzero , refl }
    ; i = fzero
    ; k = fsuc fzero
    ; distinct = λ ()
    ; merged = refl
    }
