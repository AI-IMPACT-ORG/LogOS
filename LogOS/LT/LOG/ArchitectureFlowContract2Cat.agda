{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ArchitectureFlowContract2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Flow + contract stack over the architectural boundary basis `LOGᴳ`.

open import LogOS.Prelude
import LogOS.LT.LOG.ImplementationFlow2Cat.Core as FlowArchitecture
import LogOS.LT.LOG.ImplementationContract2Cat.Core as ContractArchitecture
import LogOS.LT.Ports.Template.Stack2Cat as Template

module Ports {ℓ ℓRel ℓCode : Level} =
  Template.BinarySingletonStackExports
    (FlowArchitecture.flowSingleton {ℓ} {ℓRel} {ℓCode})
    (ContractArchitecture.contractSingleton {ℓ} {ℓRel} {ℓCode})
open Ports public using
  ( stack2Cat
  ; stack
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )
