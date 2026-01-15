{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.SyntaxCore where

open import Data.List using (List; []; _∷_; _++_)

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)
import LogOS.Packs.Agents.Emit.IR.BackendSyntax as BackendSyntax

module For (B : Backend) where
  module Py = BackendSyntax.For B

  PyExpr : Set
  PyExpr = Py.PyExpr

  PyArg : Set
  PyArg = Py.PyArg

  tf : PyExpr
  tf = Py.pyVar "tf"

  keras : PyExpr
  keras = Py.pyAttr tf "keras"

  layers : PyExpr
  layers = Py.pyAttr keras "layers"

  schedules : PyExpr
  schedules = Py.pyAttr (Py.pyAttr keras "optimizers") "schedules"

  linalg : PyExpr
  linalg = Py.pyAttr tf "linalg"

  float32 : PyExpr
  float32 = Py.pyAttr tf "float32"

  kerasInput : List PyArg → PyExpr
  kerasInput args = Py.pyCall (Py.pyAttr keras "Input") args

  kerasModel : PyExpr → PyExpr → PyExpr
  kerasModel inp out = Py.pyCall2 (Py.pyAttr keras "Model") inp out

  tfRange : PyExpr → PyExpr
  tfRange n = Py.pyCall1 (Py.pyAttr tf "range") n

  tfShape : PyExpr → PyExpr
  tfShape x = Py.pyCall1 (Py.pyAttr tf "shape") x

  reduceMean : List PyArg → PyExpr
  reduceMean args = Py.pyCall (Py.pyAttr tf "reduce_mean") args

  timestamp : PyExpr
  timestamp = Py.pyCall0 (Py.pyAttr tf "timestamp")

  tfSize : PyExpr → PyExpr
  tfSize x = Py.pyCall1 (Py.pyAttr tf "size") x

  tfCast : PyExpr → PyExpr → PyExpr
  tfCast value dtype = Py.pyCall2 (Py.pyAttr tf "cast") value dtype

  globalNorm : PyExpr → PyExpr
  globalNorm grads = Py.pyCall1 (Py.pyAttr linalg "global_norm") grads

  embedding : PyExpr → PyExpr → PyExpr → PyExpr
  embedding vocab dim x =
    Py.pyCall1 (Py.pyCall2 (Py.pyAttr layers "Embedding") vocab dim) x

  dense : PyExpr → PyExpr → PyExpr
  dense units x = Py.pyCall1 (Py.pyCall1 (Py.pyAttr layers "Dense") units) x

  denseAct : PyExpr → PyExpr → PyExpr → PyExpr
  denseAct units act x =
    Py.pyCall1
      (Py.pyCall (Py.pyAttr layers "Dense")
        (Py.pyPos units ∷ Py.pyKw "activation" act ∷ []))
      x

  layerNorm : PyExpr → PyExpr → PyExpr
  layerNorm eps x =
    Py.pyCall1
      (Py.pyCall (Py.pyAttr layers "LayerNormalization")
        (Py.pyKw "epsilon" eps ∷ []))
      x

  multiHeadAttentionBase
    : PyExpr → PyExpr → PyExpr → List PyArg → List PyArg → PyExpr
  multiHeadAttentionBase heads keyDim dropout extra args =
    Py.pyCall
      (Py.pyCall (Py.pyAttr layers "MultiHeadAttention")
        (( Py.pyKw "num_heads" heads ∷
           Py.pyKw "key_dim" keyDim ∷
           Py.pyKw "dropout" dropout ∷
           [] )
         ++ extra))
      args

  multiHeadAttentionWith
    : PyExpr → PyExpr → PyExpr → List PyArg → PyExpr → PyExpr
  multiHeadAttentionWith heads keyDim dropout extra x =
    multiHeadAttentionBase heads keyDim dropout extra
      (Py.pyPos x ∷ Py.pyPos x ∷ [])

  multiHeadAttentionKV
    : PyExpr → PyExpr → PyExpr → List PyArg → PyExpr → PyExpr → PyExpr
  multiHeadAttentionKV heads keyDim dropout extra query value =
    multiHeadAttentionBase heads keyDim dropout extra
      (Py.pyPos query ∷ Py.pyPos value ∷ [])

  multiHeadAttentionQKV
    : PyExpr → PyExpr → PyExpr → List PyArg → PyExpr → PyExpr → PyExpr → PyExpr
  multiHeadAttentionQKV heads keyDim dropout extra query value key =
    multiHeadAttentionBase heads keyDim dropout extra
      (Py.pyPos query ∷ Py.pyPos value ∷ Py.pyPos key ∷ [])

  multiHeadAttention
    : PyExpr → PyExpr → PyExpr → PyExpr → PyExpr
  multiHeadAttention heads keyDim dropout x =
    multiHeadAttentionWith heads keyDim dropout [] x

  polynomialDecay : PyExpr → PyExpr → PyExpr → PyExpr
  polynomialDecay initLR decaySteps endLR =
    Py.pyCall
      (Py.pyAttr schedules "PolynomialDecay")
      ( Py.pyKw "initial_learning_rate" initLR ∷
        Py.pyKw "decay_steps" decaySteps ∷
        Py.pyKw "end_learning_rate" endLR ∷
        [] )
