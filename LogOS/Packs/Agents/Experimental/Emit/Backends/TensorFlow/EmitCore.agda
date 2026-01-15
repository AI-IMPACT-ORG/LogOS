{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.EmitCore where

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)

module For (B : Backend) where
  
  open import LogOS.Prelude
  
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat using (ℕ)
  open import Data.String using (String; _++s_; intercalateS)
  open import LogOS.Base.Signature using (LogOSSignature)
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.Minimal.Con using (BulkBoundary)
  open import LogOS.Minimal.Truth as Truth
  open import LogOS.Kernel.Graded using (GradedKernel)
  import LogOS.Packs.Agents.Emit.IR.BackendSyntax as BackendSyntax
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.SyntaxCore as SyntaxCore
  import LogOS.Packs.Agents.Emit.IR.Intent as Intent
  import LogOS.Packs.Agents.Emit.IR.IntentExamples as Examples
  import LogOS.Packs.Agents.Emit.IR.IntentFactory as Factory
  open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.DataPlan as DataPlan
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Pipeline as Pipeline
  import LogOS.Packs.Agents.Emit.IR.Features.TelemetryPlan as Plan
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Telemetry as TelemetryFeature
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Coupling as CouplingFeature
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Symbolic as SymbolicFeature

  module Py = BackendSyntax.For B
  module TFS = SyntaxCore.For B
  module Telemetry = TelemetryFeature.For B
  module Coupling = CouplingFeature.For B
  module Symbolic = SymbolicFeature.For B
  
  -- Minimal Python/TensorFlow emitter for a transformer-like training loop.
  
  open Intent using (param; literal; litNat)
  
  paramNames : List TFArg → List String
  paramNames [] = []
  paramNames (param name ∷ xs) = name ∷ paramNames xs
  paramNames (literal _ ∷ xs) = paramNames xs
  
  buildArgs : Intent.ModelFamily → TFHyperParams → List String
  buildArgs Intent.decoderOnly h =
    paramNames
      ( TFHyperParams.tgtVocab h ∷
        TFHyperParams.modelDim h ∷
        TFHyperParams.headCount h ∷
        TFHyperParams.layerCount h ∷
        TFHyperParams.ffnDim h ∷
        TFHyperParams.maxLen h ∷
        TFHyperParams.dropout h ∷
        [] )
  buildArgs Intent.encoderDecoder h =
    paramNames
      ( TFHyperParams.srcVocab h ∷
        TFHyperParams.tgtVocab h ∷
        TFHyperParams.modelDim h ∷
        TFHyperParams.headCount h ∷
        TFHyperParams.layerCount h ∷
        TFHyperParams.ffnDim h ∷
        TFHyperParams.maxLen h ∷
        TFHyperParams.dropout h ∷
        [] )
  buildArgs Intent.mlpBaseline h =
    paramNames
      ( TFHyperParams.tgtVocab h ∷
        TFHyperParams.modelDim h ∷
        TFHyperParams.layerCount h ∷
        TFHyperParams.ffnDim h ∷
        TFHyperParams.dropout h ∷
        [] )
  
  paramList : TFHyperParams → String
  paramList h = intercalateS ", " (buildArgs Intent.decoderOnly h)
  
  trainArgs : TFTrainingParams → List String
  trainArgs t =
    TFTrainingParams.datasetVar t ∷
    paramNames (TFTrainingParams.epochs t ∷ TFTrainingParams.learningRate t ∷ [])
  
  trainSig : TFTrainingParams → String
  trainSig t =
    "def train(model, " ++s intercalateS ", " (trainArgs t) ++s "):"
  
  record TFEmitMeta : Set where
    field
      buildParams : List String
      trainParams : List String
  
  emitMeta : TFEmitSpec → TFEmitMeta
  emitMeta spec =
    let h = TFEmitSpec.hyper spec
        t = TFEmitSpec.train spec
        f = TFEmitSpec.family spec
    in
    record
      { buildParams = buildArgs f h
      ; trainParams = trainArgs t
      }
  
  record TFEmitResult : Set where
    field
      pyModule : Py.PyModule
      meta : TFEmitMeta
  
  hasCausalMask : List Intent.ModelConstraint → Bool
  hasCausalMask [] = false
  hasCausalMask (Intent.causalMask ∷ _) = true
  hasCausalMask (Intent.noDropout ∷ xs) = hasCausalMask xs
  
  hasNoDropout : List Intent.ModelConstraint → Bool
  hasNoDropout [] = false
  hasNoDropout (Intent.noDropout ∷ _) = true
  hasNoDropout (Intent.causalMask ∷ xs) = hasNoDropout xs
  
  hasShiftRight : List Intent.DataOp → Bool
  hasShiftRight [] = false
  hasShiftRight (Intent.shiftRight ∷ _) = true
  
  orBool : Bool → Bool → Bool
  orBool true _ = true
  orBool false b = b
  
  andBool : Bool → Bool → Bool
  andBool true b = b
  andBool false _ = false
  
  ifBool : ∀ {A : Set} → Bool → A → A → A
  ifBool true x _ = x
  ifBool false _ y = y
  
  effectiveDropout : TFHyperParams → TFArg
  effectiveDropout h with hasNoDropout (TFHyperParams.constraints h)
  ... | true = literal "0.0"
  ... | false = TFHyperParams.dropout h
  
  
  tfArgExpr : TFArg → Py.PyExpr
  tfArgExpr (param s) = Py.pyVar s
  tfArgExpr (literal s) = Py.pyRaw s
  
  lossExpr : TFLoss → Py.PyExpr
  lossExpr Intent.sparseCategorical =
    Py.pyCall
      (Py.pyAttr (Py.pyAttr TFS.keras "losses") "SparseCategoricalCrossentropy")
      ( Py.pyKw "from_logits" Py.pyTrue ∷
        Py.pyKw "reduction" (Py.pyString "none") ∷
        [] )
  lossExpr (Intent.customLoss s) = Py.pyRaw s
  
  optimizerCtor : TFOptimizer → Py.PyExpr
  optimizerCtor opt =
    Py.pyAttr (Py.pyAttr TFS.keras "optimizers")
      (renderOptimizer opt)
  
  
  targetPattern : List String → Py.PyTarget
  targetPattern [] = Py.targetName "_"
  targetPattern (x ∷ []) = Py.targetName x
  targetPattern (x ∷ y ∷ xs) = Py.targetTuple (x ∷ y ∷ xs)
  
  effectiveTargetName : TFTrainingParams → String
  effectiveTargetName t =
    let plan = DataPlan.dataPlan t in
    ifBool (DataPlan.DataPlan.hasTargets plan)
      (TFTrainingParams.targetVar t)
      (TFTrainingParams.inputVar t)
  
  sliceBatchTo : Py.PyExpr → Py.PyExpr → Py.PyExpr
  sliceBatchTo tokens end =
    Py.pySubscript tokens (Py.pySliceFull ∷ Py.pySliceTo end ∷ [])
  
  sliceBatchFrom : Py.PyExpr → Py.PyExpr → Py.PyExpr
  sliceBatchFrom tokens start =
    Py.pySubscript tokens (Py.pySliceFull ∷ Py.pySliceFrom start ∷ [])
  
  preprocessDef : TFTrainingParams → List Py.PyStmt
  preprocessDef t =
    let plan = DataPlan.dataPlan t
        inputName = TFTrainingParams.inputVar t
        targetName = TFTrainingParams.targetVar t
        taskName = TFTrainingParams.taskVar t
        hasTask = DataPlan.DataPlan.hasTask plan
        params =
          ifBool hasTask (taskName ∷ "batch" ∷ []) ("batch" ∷ [])
        outTuple =
          ifBool hasTask
            (Py.pyTuple
              ( Py.pyVar taskName ∷
                Py.pyVar inputName ∷
                Py.pyVar targetName ∷
                [] ))
            (Py.pyTuple (Py.pyVar inputName ∷ Py.pyVar targetName ∷ []))
        body =
          Py.pyAssign "tokens" (Py.pyVar "batch")
          ∷ Py.pyAssign inputName
              (sliceBatchTo (Py.pyVar "tokens") (Py.pyRaw "-1"))
          ∷ Py.pyAssign targetName
              (sliceBatchFrom (Py.pyVar "tokens") (Py.pyRaw "1"))
          ∷ Py.pyReturn outTuple
          ∷ []
    in
    ifBool (DataPlan.DataPlan.needsPreprocess plan)
      (Py.pyDef "preprocess" params body ∷ Py.pyBlank ∷ [])
      []
  
  datasetMapStmts : TFTrainingParams → DataPlan.DataPlan → List Py.PyStmt
  datasetMapStmts t plan with DataPlan.DataPlan.needsPreprocess plan
  ... | false = []
  ... | true =
    let datasetName = TFTrainingParams.datasetVar t
    in
    Py.pyAssign datasetName
      (Py.pyCall1 (Py.pyAttr (Py.pyVar datasetName) "map") (Py.pyVar "preprocess"))
      ∷ []
  
  scheduleStmts : TFTrainingParams → List Py.PyStmt
  scheduleStmts t with TFTrainingParams.schedule t
  ... | Intent.constant = []
  ... | Intent.linearDecay decaySteps endLR =
    Py.pyAssign "lr_schedule"
      (TFS.polynomialDecay
        (tfArgExpr (TFTrainingParams.learningRate t))
        (tfArgExpr decaySteps)
        (tfArgExpr endLR))
      ∷ []
  
  learningRateExpr : TFTrainingParams → Py.PyExpr
  learningRateExpr t with TFTrainingParams.schedule t
  ... | Intent.constant = tfArgExpr (TFTrainingParams.learningRate t)
  ... | Intent.linearDecay _ _ = Py.pyVar "lr_schedule"
  
  shiftTargetsForFamily : Intent.ModelFamily → Bool → Bool
  shiftTargetsForFamily Intent.encoderDecoder shift = shift
  shiftTargetsForFamily Intent.decoderOnly _ = false
  shiftTargetsForFamily Intent.mlpBaseline _ = false
  
  targetInName : String → String
  targetInName name = name ++s "_in"
  
  targetOutName : String → String
  targetOutName name = name ++s "_out"
  
  shiftTargetStmts : Bool → String → List Py.PyStmt
  shiftTargetStmts false _ = []
  shiftTargetStmts true targetName =
    Py.pyAssign (targetInName targetName)
      (sliceBatchTo (Py.pyVar targetName) (Py.pyRaw "-1"))
    ∷ Py.pyAssign (targetOutName targetName)
      (sliceBatchFrom (Py.pyVar targetName) (Py.pyRaw "1"))
    ∷ []
  
  modelInputExpr : Intent.ModelFamily → Bool → String → String → Py.PyExpr
  modelInputExpr Intent.decoderOnly _ inputName _ = Py.pyVar inputName
  modelInputExpr Intent.mlpBaseline _ inputName _ = Py.pyVar inputName
  modelInputExpr Intent.encoderDecoder true inputName targetName =
    Py.pyTuple (Py.pyVar inputName ∷ Py.pyVar (targetInName targetName) ∷ [])
  modelInputExpr Intent.encoderDecoder false inputName targetName =
    Py.pyTuple (Py.pyVar inputName ∷ Py.pyVar targetName ∷ [])
  
  lossTargetExpr : Bool → String → Py.PyExpr
  lossTargetExpr true targetName = Py.pyVar (targetOutName targetName)
  lossTargetExpr false targetName = Py.pyVar targetName
  
  
  
  
  modelBodyFor
    : Intent.ModelFamily
    → TFHyperParams
    → Py.PyExpr
    → Py.PyExpr
    → Py.PyExpr
    → Py.PyExpr
    → Py.PyExpr
    → List Py.PyArg
    → List Py.PyStmt
  modelBodyFor Intent.decoderOnly h relu one eps keyDim dropoutExpr causalArgs =
    let tokens = Py.pyString "tokens"
        tokInVar = Py.pyVar "tok_in"
        tokEmbVar = Py.pyVar "tok_emb"
        posVar = Py.pyVar "pos"
        posEmbVar = Py.pyVar "pos_emb"
        xVar = Py.pyVar "x"
        ffnVar = Py.pyVar "ffn"
        attnVar = Py.pyVar "attn"
        logitsVar = Py.pyVar "logits"
        shapeTok = TFS.tfShape tokInVar
        posLen = Py.pyIndex shapeTok one
        tokEmbed =
          TFS.embedding
            (tfArgExpr (TFHyperParams.tgtVocab h))
            (tfArgExpr (TFHyperParams.modelDim h))
            tokInVar
        posEmbed =
          TFS.embedding
            (tfArgExpr (TFHyperParams.maxLen h))
            (tfArgExpr (TFHyperParams.modelDim h))
            posVar
        attnCall =
          TFS.multiHeadAttentionWith
            (tfArgExpr (TFHyperParams.headCount h))
            keyDim
            dropoutExpr
            causalArgs
            xVar
        lnAttn =
          TFS.layerNorm
            eps
            (Py.pyBinOp "+" xVar attnVar)
        ffnDense =
          TFS.denseAct
            (tfArgExpr (TFHyperParams.ffnDim h))
            relu
            xVar
        ffnProj =
          TFS.dense
            (tfArgExpr (TFHyperParams.modelDim h))
            ffnVar
        lnFfn =
          TFS.layerNorm
            eps
            (Py.pyBinOp "+" xVar ffnVar)
    in
    Py.pyAssign "tok_in"
      (TFS.kerasInput
        ( Py.pyKw "shape" (Py.pyRaw "(None,)") ∷
          Py.pyKw "dtype" (Py.pyAttr TFS.tf "int32") ∷
          Py.pyKw "name" tokens ∷
          [] ))
    ∷ Py.pyAssign "tok_emb" tokEmbed
    ∷ Py.pyAssign "pos" (TFS.tfRange posLen)
    ∷ Py.pyAssign "pos_emb" posEmbed
    ∷ Py.pyAssign "x" (Py.pyBinOp "+" tokEmbVar posEmbVar)
    ∷ Py.pyForIn (Py.targetName "_")
        (Py.pyCall1 (Py.pyVar "range")
          (tfArgExpr (TFHyperParams.layerCount h)))
        ( Py.pyAssign "attn" attnCall
          ∷ Py.pyAssign "x" lnAttn
          ∷ Py.pyAssign "ffn" ffnDense
          ∷ Py.pyAssign "ffn" ffnProj
          ∷ Py.pyAssign "x" lnFfn
          ∷ [] )
    ∷ Py.pyAssign "logits"
        (TFS.dense
          (tfArgExpr (TFHyperParams.tgtVocab h))
          xVar)
    ∷ Py.pyReturn
        (TFS.kerasModel tokInVar logitsVar)
    ∷ []
  modelBodyFor Intent.encoderDecoder h relu one eps keyDim dropoutExpr causalArgs =
    let srcTokens = Py.pyString "src_tokens"
        tgtTokens = Py.pyString "tgt_tokens"
        srcInVar = Py.pyVar "src_in"
        tgtInVar = Py.pyVar "tgt_in"
        srcEmbVar = Py.pyVar "src_emb"
        tgtEmbVar = Py.pyVar "tgt_emb"
        srcPosVar = Py.pyVar "src_pos"
        tgtPosVar = Py.pyVar "tgt_pos"
        srcPosEmbVar = Py.pyVar "src_pos_emb"
        tgtPosEmbVar = Py.pyVar "tgt_pos_emb"
        encVar = Py.pyVar "enc"
        decVar = Py.pyVar "dec"
        ffnVar = Py.pyVar "ffn"
        attnVar = Py.pyVar "attn"
        crossVar = Py.pyVar "cross"
        logitsVar = Py.pyVar "logits"
        srcShape = TFS.tfShape srcInVar
        tgtShape = TFS.tfShape tgtInVar
        srcLen = Py.pyIndex srcShape one
        tgtLen = Py.pyIndex tgtShape one
        srcEmbed =
          TFS.embedding
            (tfArgExpr (TFHyperParams.srcVocab h))
            (tfArgExpr (TFHyperParams.modelDim h))
            srcInVar
        tgtEmbed =
          TFS.embedding
            (tfArgExpr (TFHyperParams.tgtVocab h))
            (tfArgExpr (TFHyperParams.modelDim h))
            tgtInVar
        srcPosEmbed =
          TFS.embedding
            (tfArgExpr (TFHyperParams.maxLen h))
            (tfArgExpr (TFHyperParams.modelDim h))
            srcPosVar
        tgtPosEmbed =
          TFS.embedding
            (tfArgExpr (TFHyperParams.maxLen h))
            (tfArgExpr (TFHyperParams.modelDim h))
            tgtPosVar
        encAttn =
          TFS.multiHeadAttentionWith
            (tfArgExpr (TFHyperParams.headCount h))
            keyDim
            dropoutExpr
            []
            encVar
        decSelfAttn =
          TFS.multiHeadAttentionWith
            (tfArgExpr (TFHyperParams.headCount h))
            keyDim
            dropoutExpr
            causalArgs
            decVar
        decCross =
          TFS.multiHeadAttentionQKV
            (tfArgExpr (TFHyperParams.headCount h))
            keyDim
            dropoutExpr
            []
            decVar
            encVar
            encVar
        ffnDense =
          TFS.denseAct
            (tfArgExpr (TFHyperParams.ffnDim h))
            relu
            decVar
        ffnProj =
          TFS.dense
            (tfArgExpr (TFHyperParams.modelDim h))
            ffnVar
        encFfnDense =
          TFS.denseAct
            (tfArgExpr (TFHyperParams.ffnDim h))
            relu
            encVar
        encFfnProj =
          TFS.dense
            (tfArgExpr (TFHyperParams.modelDim h))
            ffnVar
    in
    Py.pyAssign "src_in"
      (TFS.kerasInput
        ( Py.pyKw "shape" (Py.pyRaw "(None,)") ∷
          Py.pyKw "dtype" (Py.pyAttr TFS.tf "int32") ∷
          Py.pyKw "name" srcTokens ∷
          [] ))
    ∷ Py.pyAssign "tgt_in"
        (TFS.kerasInput
          ( Py.pyKw "shape" (Py.pyRaw "(None,)") ∷
            Py.pyKw "dtype" (Py.pyAttr TFS.tf "int32") ∷
            Py.pyKw "name" tgtTokens ∷
            [] ))
    ∷ Py.pyAssign "src_emb" srcEmbed
    ∷ Py.pyAssign "tgt_emb" tgtEmbed
    ∷ Py.pyAssign "src_pos" (TFS.tfRange srcLen)
    ∷ Py.pyAssign "tgt_pos" (TFS.tfRange tgtLen)
    ∷ Py.pyAssign "src_pos_emb" srcPosEmbed
    ∷ Py.pyAssign "tgt_pos_emb" tgtPosEmbed
    ∷ Py.pyAssign "enc" (Py.pyBinOp "+" srcEmbVar srcPosEmbVar)
    ∷ Py.pyAssign "dec" (Py.pyBinOp "+" tgtEmbVar tgtPosEmbVar)
    ∷ Py.pyForIn (Py.targetName "_")
        (Py.pyCall1 (Py.pyVar "range")
          (tfArgExpr (TFHyperParams.layerCount h)))
        ( Py.pyAssign "attn" encAttn
          ∷ Py.pyAssign "enc" (TFS.layerNorm eps (Py.pyBinOp "+" encVar attnVar))
          ∷ Py.pyAssign "ffn" encFfnDense
          ∷ Py.pyAssign "ffn" encFfnProj
          ∷ Py.pyAssign "enc" (TFS.layerNorm eps (Py.pyBinOp "+" encVar ffnVar))
          ∷ Py.pyAssign "attn" decSelfAttn
          ∷ Py.pyAssign "dec" (TFS.layerNorm eps (Py.pyBinOp "+" decVar attnVar))
          ∷ Py.pyAssign "cross" decCross
          ∷ Py.pyAssign "dec" (TFS.layerNorm eps (Py.pyBinOp "+" decVar crossVar))
          ∷ Py.pyAssign "ffn" ffnDense
          ∷ Py.pyAssign "ffn" ffnProj
          ∷ Py.pyAssign "dec" (TFS.layerNorm eps (Py.pyBinOp "+" decVar ffnVar))
          ∷ [] )
    ∷ Py.pyAssign "logits"
        (TFS.dense
          (tfArgExpr (TFHyperParams.tgtVocab h))
          decVar)
    ∷ Py.pyReturn
        (TFS.kerasModel (Py.pyTuple (srcInVar ∷ tgtInVar ∷ [])) logitsVar)
    ∷ []
  modelBodyFor Intent.mlpBaseline h relu one eps keyDim dropoutExpr causalArgs =
    let tokens = Py.pyString "tokens"
        tokInVar = Py.pyVar "tok_in"
        tokEmbVar = Py.pyVar "tok_emb"
        xVar = Py.pyVar "x"
        logitsVar = Py.pyVar "logits"
    in
    Py.pyAssign "tok_in"
      (TFS.kerasInput
        ( Py.pyKw "shape" (Py.pyRaw "(None,)") ∷
          Py.pyKw "dtype" (Py.pyAttr TFS.tf "int32") ∷
          Py.pyKw "name" tokens ∷
          [] ))
    ∷ Py.pyAssign "tok_emb"
        (TFS.embedding
          (tfArgExpr (TFHyperParams.tgtVocab h))
          (tfArgExpr (TFHyperParams.modelDim h))
          tokInVar)
    ∷ Py.pyAssign "x"
        (TFS.reduceMean
          (Py.pyPos tokEmbVar ∷ Py.pyKw "axis" (Py.pyRaw "1") ∷ []))
    ∷ Py.pyForIn (Py.targetName "_")
        (Py.pyCall1 (Py.pyVar "range")
          (tfArgExpr (TFHyperParams.layerCount h)))
        ( Py.pyAssign "x"
            (TFS.denseAct
              (tfArgExpr (TFHyperParams.ffnDim h))
              relu
              xVar)
          ∷ Py.pyAssign "x"
              (TFS.dense
                (tfArgExpr (TFHyperParams.modelDim h))
                xVar)
          ∷ [] )
    ∷ Py.pyAssign "logits"
        (TFS.dense
          (tfArgExpr (TFHyperParams.tgtVocab h))
          xVar)
    ∷ Py.pyReturn
        (TFS.kerasModel tokInVar logitsVar)
    ∷ []
  
  trainBodyFor
    : TFTrainingParams
    → DataPlan.DataPlan
    → Plan.TelemetryPlan
    → Bool
    → String
    → Py.PyExpr
    → Py.PyExpr
    → Intent.CouplingIntent
    → List Py.PyStmt
  trainBodyFor t plan telPlan shiftTargets targetName modelInputs lossTarget coupling =
    let true = Py.pyTrue
        one = Py.pyRaw "1"
        inputName = TFTrainingParams.inputVar t
        dataComment = DataPlan.DataPlan.comment plan
        telemetryEnabled = Plan.TelemetryPlan.enabled telPlan
        continualActive = Plan.TelemetryPlan.continualActive telPlan
        needsTiming = Plan.TelemetryPlan.needTiming telPlan
        modelVar = Py.pyVar "model"
        trainableVars = Py.pyAttr modelVar "trainable_variables"
        stepInitStmts =
          ifBool telemetryEnabled
            (Py.pyAssign "step" (Py.pyRaw "0") ∷ [])
            []
        continualInitStmts =
          ifBool continualActive
            ( Py.pyAssign "task_best" (Py.pyRaw "{}")
              ∷ Py.pyAssign "loss_ema" (Py.pyRaw "0.0")
              ∷ [] )
            []
        stepStartStmts =
          ifBool needsTiming
            ( Py.pyAssign "step_start"
                TFS.timestamp ∷ [] )
            []
        stepIncStmts =
          ifBool telemetryEnabled
            (Py.pyAssign "step"
              (Py.pyBinOp "+" (Py.pyVar "step") one) ∷ [])
            []
        telemetryStmts =
          ifBool telemetryEnabled
            ( Py.pyIf (Telemetry.telemetryStepCond (TFTrainingParams.telemetry t))
                (Telemetry.telemetryBody t telPlan)
              ∷ [] )
            []
        couplingApplyStmts =
          Coupling.couplingApplyStmts coupling inputName lossTarget
        lossLine =
          Py.pyAssign "loss"
            (TFS.reduceMean
              (Py.pyPos
                (Py.pyCall (Py.pyVar "loss_fn")
                  ( Py.pyPos lossTarget ∷
                    Py.pyPos (Py.pyVar "logits") ∷
                    [] ))
              ∷ [] ))
    in
    ( Py.pyComment dataComment
      ∷ Py.pyAssign "loss_fn" (lossExpr (TFTrainingParams.loss t))
      ∷ [] )
    ++ scheduleStmts t
    ++ datasetMapStmts t plan
    ++ ( Py.pyAssign "optimizer"
          (Py.pyCall1 (optimizerCtor (TFTrainingParams.optimizer t))
            (learningRateExpr t))
        ∷ [] )
    ++ stepInitStmts
    ++ continualInitStmts
    ++ ( Py.pyForIn (Py.targetName "epoch")
          (Py.pyCall1 (Py.pyVar "range")
            (tfArgExpr (TFTrainingParams.epochs t)))
          ( Py.pyForIn
              (targetPattern (DataPlan.DataPlan.datasetVars plan))
              (Py.pyVar (TFTrainingParams.datasetVar t))
                  ( stepStartStmts
                    ++ shiftTargetStmts shiftTargets targetName
                    ++ ( Py.pyWithAs (Py.pyCall0 (Py.pyAttr TFS.tf "GradientTape")) "tape"
                          ( ( Py.pyAssign "logits"
                                (Py.pyCall (Py.pyVar "model")
                                  ( Py.pyPos modelInputs ∷
                                    Py.pyKw "training" true ∷
                                    [] ))
                              ∷ [] )
                            ++ couplingApplyStmts
                            ++ ( lossLine ∷ [] ) )
                        ∷ Py.pyAssign "grads"
                            (Py.pyCall (Py.pyAttr (Py.pyVar "tape") "gradient")
                              ( Py.pyPos (Py.pyVar "loss") ∷
                                Py.pyPos trainableVars ∷
                            [] ))
                    ∷ Py.pyExprStmt
                        (Py.pyCall1 (Py.pyAttr (Py.pyVar "optimizer") "apply_gradients")
                          (Py.pyCall (Py.pyVar "zip")
                            ( Py.pyPos (Py.pyVar "grads") ∷
                              Py.pyPos trainableVars ∷
                              [] )))
                    ∷ [] )
                ++ stepIncStmts
                ++ telemetryStmts )
              ∷ [] )
        ∷ [] )
  
  emitModuleWith : TFEmitSpec → TFEmitMeta → Py.PyModule
  emitModuleWith spec meta =
    let h = TFEmitSpec.hyper spec
        t = TFEmitSpec.train spec
        f = TFEmitSpec.family spec
        relu = Py.pyString "relu"
        true = Py.pyTrue
        one = Py.pyRaw "1"
        eps = Py.pyRaw "1e-5"
        plan = Pipeline.planFromSpec spec
        dataPlan = Pipeline.EmitPlan.dataPlan plan
        telPlan = Pipeline.EmitPlan.telemetryPlan plan
        caps = Pipeline.EmitPlan.caps plan
        keyDim =
          Py.pyBinOp "//"
            (tfArgExpr (TFHyperParams.modelDim h))
            (tfArgExpr (TFHyperParams.headCount h))
        dropoutExpr = tfArgExpr (effectiveDropout h)
        causalArgs =
          ifBool (hasCausalMask (TFHyperParams.constraints h))
            (Py.pyKw "use_causal_mask" true ∷ [])
            []
        inputName = TFTrainingParams.inputVar t
        targetName =
          ifBool (DataPlan.DataPlan.hasTargets dataPlan)
            (TFTrainingParams.targetVar t)
            (TFTrainingParams.inputVar t)
        hasTargets = DataPlan.DataPlan.hasTargets dataPlan
        shiftTargets =
          andBool
            (shiftTargetsForFamily f (hasShiftRight (TFTrainingParams.dataOps t)))
            hasTargets
        modelInputs = modelInputExpr f shiftTargets inputName targetName
        lossTarget = lossTargetExpr shiftTargets targetName
        symbolic = TFEmitSpec.symbolic spec
        coupling = TFEmitSpec.coupling spec
        symbolicStmts =
          ifBool (Pipeline.FeatureCaps.symbolic caps)
            (Symbolic.symbolicComments symbolic)
            []
        couplingStmts =
          ifBool (Pipeline.FeatureCaps.coupling caps)
            (Coupling.couplingComments coupling ++ Coupling.couplingDef coupling)
            []
        modelBody = modelBodyFor f h relu one eps keyDim dropoutExpr causalArgs
        trainBody =
          trainBodyFor t dataPlan telPlan shiftTargets targetName
            modelInputs lossTarget coupling
    in
    Py.pyModule
      ( Py.licenseHeader ++
        ( Py.pyImportAs "tensorflow" "tf"
          ∷ Py.pyBlank
          ∷ [] )
        ++ symbolicStmts
        ++ couplingStmts
        ++ preprocessDef t
        ++ ( Py.pyDef "build_model" (TFEmitMeta.buildParams meta) modelBody
          ∷ Py.pyBlank
          ∷ Py.pyDef "train" ("model" ∷ TFEmitMeta.trainParams meta) trainBody
          ∷ [] ) )
  
  emitModule : TFEmitSpec → Py.PyModule
  emitModule spec = emitModuleWith spec (emitMeta spec)
  
  emitConfig : TFEmitSpec → TFEmitResult
  emitConfig spec =
    let meta = emitMeta spec in
    record { pyModule = emitModuleWith spec meta; meta = meta }
  
  renderConfig : TFEmitResult → String
  renderConfig result = Py.renderModule (TFEmitResult.pyModule result)
  
  emitPython : TFEmitSpec → String
  emitPython spec = renderConfig (emitConfig spec)
  
  emitConfigFromIntent : Intent.EmitIntent → TFEmitResult
  emitConfigFromIntent intent = emitConfig (emitSpecFromIntent intent)
  
  emitPythonFromIntent : Intent.EmitIntent → String
  emitPythonFromIntent intent = renderConfig (emitConfigFromIntent intent)
  
  emitConfigFromFactory : Factory.FactoryKey → TFEmitResult
  emitConfigFromFactory key = emitConfigFromIntent (Factory.intentFor key)
  
  emitPythonFromFactory : Factory.FactoryKey → String
  emitPythonFromFactory key = renderConfig (emitConfigFromFactory key)
  
  emitPythonFactoryDefault : String
  emitPythonFactoryDefault = emitPythonFromFactory Factory.defaultFactoryKey
  
  emitPythonExample : String
  emitPythonExample = emitPythonFromIntent Examples.encoderDecoderTelemetry
  
  module WithBridge
    {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
              (BulkBoundary.bnd (GradedKernel.BB K)))
    where
  
    import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge as TransformerBridge
    module TB = TransformerBridge.For K ωCPO
    open QAdapter Q using (Scale)
  
    optimizerFromTag : TB.OptimizerTag → TFOptimizer
    optimizerFromTag TB.sgd = Intent.sgd
    optimizerFromTag TB.adam = Intent.adam

    optimizerFromTagged : ∀ {g} → TB.TaggedTraining g → TFOptimizer
    optimizerFromTagged T = optimizerFromTag (TB.TaggedTraining.tag T)

    optimizerFromSGD : ∀ {g} → TB.SGDTraining g → TFOptimizer
    optimizerFromSGD _ = optimizerFromTag TB.sgd

    optimizerFromAdam : ∀ {g} → TB.AdamTraining g → TFOptimizer
    optimizerFromAdam _ = optimizerFromTag TB.adam
  
    lossFromNextToken : ∀ {B} → TB.NextTokenLossObservableFromData B → TFLoss
    lossFromNextToken _ = Intent.sparseCategorical
  
    record TFTrainingHooks (g : Scale) : Set (lsuc (lsuc ℓ)) where
      field
        spec : TB.TrainingSpec g
        optimizer : TFOptimizer
        loss : TFLoss
  
    defaultTrainingParamsFromHooks
      : ∀ {g} → TFTrainingHooks g → TFTrainingParams
    defaultTrainingParamsFromHooks hooks =
      record
        { datasetVar = "dataset"
        ; inputVar = "x"
        ; targetVar = "y"
        ; taskVar = "task_id"
        ; learningRate = param "learning_rate"
        ; epochs = param "epochs"
        ; optimizer = TFTrainingHooks.optimizer hooks
        ; loss = TFTrainingHooks.loss hooks
        ; schedule = Intent.constant
        ; dataShape = Intent.paired
        ; dataOps = []
        ; telemetry = Intent.defaultTelemetry
        }
  
    emitSpecFromHooks : ∀ {g} → TFHyperParams → TFTrainingHooks g → TFEmitSpec
    emitSpecFromHooks h hooks =
      record
        { family = Intent.decoderOnly
        ; hyper = h
        ; train = defaultTrainingParamsFromHooks hooks
        ; symbolic = Intent.defaultSymbolic
        ; coupling = Intent.defaultCoupling
        }
