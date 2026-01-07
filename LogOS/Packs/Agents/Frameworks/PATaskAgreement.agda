{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.PATaskAgreement where

open import LogOS.Prelude

import LogOS.Computation.Scheme as Sch
import LogOS.Domain.UniversalIR.Schemes as US
import LogOS.Domain.UniversalIR.Theorems as UThm

-- Re-export the paper-facing agreement statement (machine schemes).
open import LogOS.Packs.UniversalIR.Agreement public
  using (ParadigmsRunEq; patask-paradigms-runEq; five-paradigm-agreement)

-- Agreement for the universal-process choices (schemes built from Choices).

record ChoiceSchemesRunEq : Set where
  field
    minsky≈lambda   : Sch.RunEq US.minskyScheme US.lambdaScheme
    lambda≈ethereum : Sch.RunEq US.lambdaScheme US.ethereumScheme
    ethereum≈oracle : Sch.RunEq US.ethereumScheme US.oracleScheme
    oracle≈circuit  : Sch.RunEq US.oracleScheme US.quantumCircuitScheme

patask-choiceSchemes-runEq : ChoiceSchemesRunEq
patask-choiceSchemes-runEq =
  record
    { minsky≈lambda = λ t →
        trans (UThm.minskyChoiceScheme≡run t)
              (trans (UThm.minsky-correct t)
                     (trans (sym (UThm.lambda-correct t))
                            (sym (UThm.lambdaChoiceScheme≡run t))))
    ; lambda≈ethereum = λ t →
        trans (UThm.lambdaChoiceScheme≡run t)
              (trans (UThm.lambda-correct t)
                     (trans (sym (UThm.ethereum-correct t))
                            (sym (UThm.ethereumChoiceScheme≡run t))))
    ; ethereum≈oracle = λ t →
        trans (UThm.ethereumChoiceScheme≡run t)
              (trans (UThm.ethereum-correct t)
                     (trans (sym (UThm.oracle-correct t))
                            (sym (UThm.oracleChoiceScheme≡run t))))
    ; oracle≈circuit = λ t →
        trans (UThm.oracleChoiceScheme≡run t)
              (trans (UThm.oracle-correct t)
                     (trans (sym (UThm.circuit-correct t))
                            (sym (UThm.circuitChoiceScheme≡run t))))
    }
