{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Interpretation.Pipeline where

-- Pipeline record (debuggable intermediate stages) + bulk parser.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  ; reverse
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using (Sig)

open import LogOS.Apps.ZFC.Metamath.SetMM.Vars using
  ( Vars
  ; varsFromHyps
  ; setVars
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using (PFormula)
open import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Support using (ParseRun)
open import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Wff using (parse⊢Bulk)

import LogOS.Apps.ZFC.Metamath.Interpretation.Close as Close
open Close using (close⊢Tokens)

record ConclPipeline : Set where
  field
    vars        : Vars
    allSetVars  : List ℕ
    closedConcl : List ℕ
    parsedConcl : PFormula

open ConclPipeline public

record ConclPipelineWithRest : Set where
  field
    vars        : Vars
    allSetVars  : List ℕ
    closedConcl : List ℕ
    closedRest  : List ℕ
    parsedConcl : PFormula

open ConclPipelineWithRest public

-- Parse the conclusion, after closing it under implicit outer ∀ over set vars.
mutual
  parseClosedConclWithEnvBulk
    : Sig
    → (hyps  : List (List ℕ))
    → (free  : List ℕ)
    → (concl : List ℕ)
    → Maybe ConclPipelineWithRest
  parseClosedConclWithEnvBulk S hyps free concl =
    varsFromHyps S hyps >>= λ V →
      let
        -- `varsFromHyps` collects by cons; reverse to preserve scan order.
        all : List ℕ
        all = reverse (setVars V)
      in
      close⊢Tokens S all concl >>= λ concl' →
      parse⊢Bulk S V free concl' >>= λ run →
      just
        (record
          { vars = V
          ; allSetVars = all
          ; closedConcl = concl'
          ; closedRest = ParseRun.rest run
          ; parsedConcl = ParseRun.value run
          })

  parseClosedConcl
    : Sig
    → (hyps  : List (List ℕ))
    → (concl : List ℕ)
    → Maybe ConclPipeline
  parseClosedConcl S hyps concl =
    parseClosedConclWithEnv S hyps [] concl

  -- Parse the same shape conclusion with an explicit free-variable environment.
  parseClosedConclWithEnv
    : Sig
    → (hyps  : List (List ℕ))
    → (free  : List ℕ)
    → (concl : List ℕ)
    → Maybe ConclPipeline
  parseClosedConclWithEnv S hyps free concl =
    parseClosedConclWithEnvBulk S hyps free concl >>= λ P →
    maybeFromExactConcl P
    where
      maybeFromExactConcl : ConclPipelineWithRest → Maybe ConclPipeline
      maybeFromExactConcl Q with ConclPipelineWithRest.closedRest Q
      ... | [] = just
        (record
          { vars = ConclPipelineWithRest.vars Q
          ; allSetVars = ConclPipelineWithRest.allSetVars Q
          ; closedConcl = ConclPipelineWithRest.closedConcl Q
          ; parsedConcl = ConclPipelineWithRest.parsedConcl Q })
      ... | _ ∷ _ = nothing
