{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.IR.IntentExamples where

open import LogOS.Prelude.Bool using (true; false)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Packs.Agents.Emit.IR.Intent

encoderDecoderTelemetry : EmitIntent
encoderDecoderTelemetry =
  record
    { model =
        record
          { family = encoderDecoder
          ; srcVocab = param "src_vocab"
          ; tgtVocab = param "tgt_vocab"
          ; modelDim = param "d_model"
          ; headCount = param "n_heads"
          ; layerCount = param "n_layers"
          ; ffnDim = param "d_ff"
          ; maxLen = param "max_len"
          ; dropout = param "dropout"
          ; constraints = causalMask ∷ []
          }
    ; dataIntent =
        record
          { datasetVar = "dataset"
          ; inputVar = "src"
          ; targetVar = "tgt"
          ; taskVar = "task_id"
          ; shape = taskPaired
          ; pipeline = shiftRight ∷ []
          }
    ; training =
        record
          { epochs = param "epochs"
          ; learningRate = param "learning_rate"
          ; schedule = linearDecay (param "decay_steps") (literal "0.0")
          ; optimizer = adam
          ; loss = sparseCategorical
          }
    ; telemetry =
        record
          { signals =
              lossCurve ∷ gradNorm ∷ stepTime ∷ tokensPerSecond ∷
              taskId ∷ taskLoss ∷ forgettingProxy ∷ driftScore ∷ []
          ; everySteps = param "log_every"
          ; continual =
              record
                { enabled = true
                ; emaAlpha = param "ema_alpha"
                ; taskVar = "task_id"
                ; bufferVar = "replay_buffer"
                }
          }
    ; symbolic =
        record
          { constraints =
              invariant "type-preservation" ∷
              rewriteRule "close-attention" ∷
              safetyBarrier "no-secret-leak" ∷
              []
          ; proofObligations = "stability-under-shift" ∷ []
          ; notes = "hybrid: constraint-guided decoding" ∷ []
          }
    ; coupling =
        record
          { strategies = guidedDecode ∷ constraintProjection ∷ lossPenalty ∷ []
          ; strength = param "coupling_strength"
          ; schedule = linearDecay (param "coupling_decay_steps") (literal "0.0")
          ; notes = "project logits onto symbolic constraints" ∷ []
          }
    }

decoderTokensTelemetry : EmitIntent
decoderTokensTelemetry =
  record
    { model =
        record
          { family = decoderOnly
          ; srcVocab = param "vocab_size"
          ; tgtVocab = param "vocab_size"
          ; modelDim = param "d_model"
          ; headCount = param "n_heads"
          ; layerCount = param "n_layers"
          ; ffnDim = param "d_ff"
          ; maxLen = param "max_len"
          ; dropout = param "dropout"
          ; constraints = causalMask ∷ []
          }
    ; dataIntent =
        record
          { datasetVar = "dataset"
          ; inputVar = "x"
          ; targetVar = "y"
          ; taskVar = "task_id"
          ; shape = taskTokens
          ; pipeline = shiftRight ∷ []
          }
    ; training =
        record
          { epochs = param "epochs"
          ; learningRate = param "learning_rate"
          ; schedule = constant
          ; optimizer = adam
          ; loss = sparseCategorical
          }
    ; telemetry =
        record
          { signals = lossCurve ∷ tokensPerSecond ∷ taskId ∷ []
          ; everySteps = param "log_every"
          ; continual =
              record
                { enabled = true
                ; emaAlpha = param "ema_alpha"
                ; taskVar = "task_id"
                ; bufferVar = "replay_buffer"
                }
          }
    ; symbolic = defaultSymbolic
    ; coupling =
        record
          { strategies = guidedDecode ∷ []
          ; strength = param "coupling_strength"
          ; schedule = constant
          ; notes = "soft-guided decoding hook" ∷ []
          }
    }

mlpBaselineQuick : EmitIntent
mlpBaselineQuick =
  record
    { model =
        record
          { family = mlpBaseline
          ; srcVocab = param "vocab_size"
          ; tgtVocab = param "vocab_size"
          ; modelDim = param "d_model"
          ; headCount = param "n_heads"
          ; layerCount = param "n_layers"
          ; ffnDim = param "d_ff"
          ; maxLen = param "max_len"
          ; dropout = literal "0.0"
          ; constraints = noDropout ∷ []
          }
    ; dataIntent =
        record
          { datasetVar = "dataset"
          ; inputVar = "x"
          ; targetVar = "y"
          ; taskVar = "task_id"
          ; shape = tokensOnly
          ; pipeline = []
          }
    ; training =
        record
          { epochs = param "epochs"
          ; learningRate = param "learning_rate"
          ; schedule = constant
          ; optimizer = adam
          ; loss = sparseCategorical
          }
    ; telemetry =
        record
          { signals = lossCurve ∷ []
          ; everySteps = param "log_every"
          ; continual = defaultContinual
          }
    ; symbolic = defaultSymbolic
    ; coupling = defaultCoupling
    }
