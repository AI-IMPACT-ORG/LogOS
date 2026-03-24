{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Irreversibility.BitResetCompression where

-- Bit reset as finite loss under a coarser process-induced public observation.

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
open import LogOS.Prelude.Fin using (fzero; fsuc; _≢_)
open import LogOS.Prelude.FiniteFamily using (FiniteFamily)
open import LogOS.Prelude.Nat.Order using (_≤ℕ_)
open import LogOS.LT.ConPreorder using (MonoMap; _≈_; ≈-sym)
open import LogOS.LT.View using (View; idView; pullbackView)
open import LogOS.LT.View.Factorisation using (FactorisesThrough; mapFactorisation)
open import LogOS.Ports.Opacity.Distinguishability using
  ( DistinguishableFamily
  ; family
  )
open import LogOS.Ports.Opacity.FiniteCompression using
  ( FiniteCompressionWitness
  ; finiteLoss-strictGap
  )

import LogOS.Apps.Irreversibility.BitReset as BitReset

privateView : View BitReset.Bit BitReset.BitPreorder
privateView = idView BitReset.BitPreorder

publicView : View BitReset.Bit BitReset.BitPreorder
publicView = pullbackView BitReset.resetBoundary (idView BitReset.BitPreorder)

resetBoundary-mono : MonoMap BitReset.BitPreorder BitReset.BitPreorder BitReset.resetBoundary
resetBoundary-mono = λ { refl → refl }

resetFactorisation : FactorisesThrough privateView publicView
resetFactorisation =
  mapFactorisation BitReset.resetBoundary resetBoundary-mono

rawSourceFamily : FiniteFamily BitReset.Bit
rawSourceFamily =
  record
    { size = suc (suc zero)
    ; at = λ where
        fzero → BitReset.zero
        (fsuc fzero) → BitReset.one
    }

sourceFamily : DistinguishableFamily privateView
sourceFamily =
  record
    { family = rawSourceFamily
    ; separated = sourceSeparated
    }
  where
    one≉zero : ¬ _≈_ BitReset.BitPreorder BitReset.one BitReset.zero
    one≉zero eq = BitReset.zero≉one (≈-sym {CP = BitReset.BitPreorder} eq)

    sourceSeparated : ∀ i j → i ≢ j → ¬ _≈_ BitReset.BitPreorder
      (FiniteFamily.at rawSourceFamily i)
      (FiniteFamily.at rawSourceFamily j)
    sourceSeparated fzero fzero neq _ = neq refl
    sourceSeparated fzero (fsuc fzero) neq = BitReset.zero≉one
    sourceSeparated (fsuc fzero) fzero neq = one≉zero
    sourceSeparated (fsuc fzero) (fsuc fzero) neq _ = neq refl

targetFamily : DistinguishableFamily publicView
targetFamily =
  record
    { family =
        record
          { size = suc zero
          ; at = λ { fzero → BitReset.zero }
          }
    ; separated = λ where
        fzero fzero neq _ → neq refl
    }

bitResetFiniteCompression
  : FiniteCompressionWitness resetFactorisation
bitResetFiniteCompression =
  record
    { source = sourceFamily
    ; target = targetFamily
    ; assign = λ _ → fzero
    ; sound = λ where
        fzero → (refl , refl)
        (fsuc fzero) → (refl , refl)
    ; surjective = λ { fzero → fzero , refl }
    ; i = fzero
    ; k = fsuc fzero
    ; distinct = λ ()
    ; merged = refl
    }

bitReset-strictGap
  : suc (FiniteFamily.size (family targetFamily))
      ≤ℕ
      FiniteFamily.size (family sourceFamily)
bitReset-strictGap = finiteLoss-strictGap bitResetFiniteCompression
