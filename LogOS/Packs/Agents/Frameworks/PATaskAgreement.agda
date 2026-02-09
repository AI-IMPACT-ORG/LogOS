{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.PATaskAgreement where

open import LogOS.Prelude

import LogOS.Computation.Scheme as Sch
import LogOS.UniversalIR.Schemes as US
import LogOS.UniversalIR.Theorems as UThm

-- Re-export the paper-facing agreement statement (machine schemes).
open import LogOS.Packs.UniversalIR.Agreement public
  using (ParadigmsRunEq; patask-paradigms-runEq; five-paradigm-agreement)

-- Agreement for the universal-process interfaces (schemes built from Interfaces).

record InterfaceSchemesRunEq : Set where
  field
    minsky≈lambda   : Sch.RunEq US.minskyScheme US.lambdaScheme
    lambda≈ethereum : Sch.RunEq US.lambdaScheme US.ethereumScheme
    ethereum≈oracle : Sch.RunEq US.ethereumScheme US.oracleScheme
    oracle≈circuit  : Sch.RunEq US.oracleScheme US.quantumCircuitScheme

patask-interfaceSchemes-runEq : InterfaceSchemesRunEq
patask-interfaceSchemes-runEq =
  record
    { minsky≈lambda = λ t →
        trans (UThm.minskyInterfaceScheme≡run t)
              (trans (UThm.minsky-correct t)
                     (trans (sym (UThm.lambda-correct t))
                            (sym (UThm.lambdaInterfaceScheme≡run t))))
    ; lambda≈ethereum = λ t →
        trans (UThm.lambdaInterfaceScheme≡run t)
              (trans (UThm.lambda-correct t)
                     (trans (sym (UThm.ethereum-correct t))
                            (sym (UThm.ethereumInterfaceScheme≡run t))))
    ; ethereum≈oracle = λ t →
        trans (UThm.ethereumInterfaceScheme≡run t)
              (trans (UThm.ethereum-correct t)
                     (trans (sym (UThm.oracle-correct t))
                            (sym (UThm.oracleInterfaceScheme≡run t))))
    ; oracle≈circuit = λ t →
        trans (UThm.oracleInterfaceScheme≡run t)
              (trans (UThm.oracle-correct t)
                     (trans (sym (UThm.circuit-correct t))
                            (sym (UThm.circuitInterfaceScheme≡run t))))
    }
