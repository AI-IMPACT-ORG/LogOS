{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.IR.IntentFactory where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String)

open import LogOS.Packs.Agents.Emit.IR.Intent
import LogOS.Packs.Agents.Emit.IR.IntentExamples as Examples

data FactoryKey : Set where
  decoderTokensTelemetry : FactoryKey
  encoderDecoderTelemetry : FactoryKey
  mlpBaselineQuick : FactoryKey

factoryKeyEq : FactoryKey → FactoryKey → Bool
factoryKeyEq decoderTokensTelemetry decoderTokensTelemetry = true
factoryKeyEq decoderTokensTelemetry encoderDecoderTelemetry = false
factoryKeyEq decoderTokensTelemetry mlpBaselineQuick = false
factoryKeyEq encoderDecoderTelemetry encoderDecoderTelemetry = true
factoryKeyEq encoderDecoderTelemetry decoderTokensTelemetry = false
factoryKeyEq encoderDecoderTelemetry mlpBaselineQuick = false
factoryKeyEq mlpBaselineQuick mlpBaselineQuick = true
factoryKeyEq mlpBaselineQuick decoderTokensTelemetry = false
factoryKeyEq mlpBaselineQuick encoderDecoderTelemetry = false

record FactoryEntry : Set where
  field
    key : FactoryKey
    name : String
    intent : EmitIntent

defaultFactoryEntry : FactoryEntry
defaultFactoryEntry =
  record
    { key = decoderTokensTelemetry
    ; name = "decoderTokensTelemetry"
    ; intent = Examples.decoderTokensTelemetry
    }

factoryEntries : List FactoryEntry
factoryEntries =
  defaultFactoryEntry ∷
  record
    { key = encoderDecoderTelemetry
    ; name = "encoderDecoderTelemetry"
    ; intent = Examples.encoderDecoderTelemetry
    } ∷
  record
    { key = mlpBaselineQuick
    ; name = "mlpBaselineQuick"
    ; intent = Examples.mlpBaselineQuick
    } ∷
  []

factoryKeys : List FactoryKey
factoryKeys = map FactoryEntry.key factoryEntries

defaultFactoryKey : FactoryKey
defaultFactoryKey = FactoryEntry.key defaultFactoryEntry

findFactoryName : FactoryKey → List FactoryEntry → String
findFactoryName _ [] = "unknown"
findFactoryName k (e ∷ es) with factoryKeyEq k (FactoryEntry.key e)
... | true = FactoryEntry.name e
... | false = findFactoryName k es

factoryKeyName : FactoryKey → String
factoryKeyName key = findFactoryName key factoryEntries

findFactory : FactoryKey → List FactoryEntry → EmitIntent
findFactory _ [] = defaultIntent
findFactory k (e ∷ es) with factoryKeyEq k (FactoryEntry.key e)
... | true = FactoryEntry.intent e
... | false = findFactory k es

intentFor : FactoryKey → EmitIntent
intentFor key = findFactory key factoryEntries
