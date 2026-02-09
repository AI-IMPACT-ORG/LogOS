{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops where

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; []; _∷_; map; zipWith)
open import LogOS.Prelude using (ℕ; zero; suc)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

-- Concrete transformer operations (forward pass), abstracted over implementation.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  record TransformerOps : Set (lsuc (lsuc ℓ)) where
    field
      Token : Set ℓ
      Scalar : Set ℓ
      Vec : Set ℓ
      Param : Set ℓ
      LayerParam : Set ℓ
      HeadParam : Set ℓ

      layers : Param → List LayerParam
      heads : LayerParam → List HeadParam

      embed : Param → Token → Vec
      positional : Param → ℕ → Vec
      readout : Param → Vec → Token

      addV : Vec → Vec → Vec
      lnAttn : LayerParam → Vec → Vec
      lnFfn : LayerParam → Vec → Vec

      qProj : HeadParam → Vec → Vec
      kProj : HeadParam → Vec → Vec
      vProj : HeadParam → Vec → Vec
      oProj : LayerParam → Vec → Vec
      ffn : LayerParam → Vec → Vec

      dot : Vec → Vec → Scalar
      scaleV : Scalar → Vec → Vec
      softmax : List Scalar → List Scalar
      sumV : List Vec → Vec
      mergeHeadsSeq : List (List Vec) → List Vec

  mapWithIndex : ∀ {A B : Set ℓ} → (ℕ → A → B) → List A → List B
  mapWithIndex {A = A} {B = B} f = go zero
    where
      go : ℕ → List A → List B
      go _ [] = []
      go i (x ∷ xs) = f i x ∷ go (suc i) xs

  withPos : ∀ (ops : TransformerOps) → TransformerOps.Param ops → List (TransformerOps.Token ops)
          → List (TransformerOps.Vec ops)
  withPos ops p toks =
    let open TransformerOps ops in
    mapWithIndex (λ i t → addV (embed p t) (positional p i)) toks

  scores : ∀ (ops : TransformerOps)
         → TransformerOps.Vec ops
         → List (TransformerOps.Vec ops)
         → List (TransformerOps.Scalar ops)
  scores ops q ks =
    let open TransformerOps ops in
    map (dot q) ks

  weights : ∀ (ops : TransformerOps)
          → TransformerOps.Vec ops
          → List (TransformerOps.Vec ops)
          → List (TransformerOps.Scalar ops)
  weights ops q ks =
    let open TransformerOps ops in
    softmax (scores ops q ks)

  attend : ∀ (ops : TransformerOps)
         → TransformerOps.Vec ops
         → List (TransformerOps.Vec ops)
         → List (TransformerOps.Vec ops)
         → TransformerOps.Vec ops
  attend ops q ks vs =
    let open TransformerOps ops in
    sumV (zipWith scaleV (weights ops q ks) vs)

  headAttention : ∀ (ops : TransformerOps)
                → TransformerOps.HeadParam ops
                → List (TransformerOps.Vec ops)
                → List (TransformerOps.Vec ops)
  headAttention ops h seq =
    let open TransformerOps ops in
    let qs = map (qProj h) seq
        ks = map (kProj h) seq
        vs = map (vProj h) seq
    in map (λ q → attend ops q ks vs) qs

  multiHead : ∀ (ops : TransformerOps)
            → TransformerOps.LayerParam ops
            → List (TransformerOps.Vec ops)
            → List (TransformerOps.Vec ops)
  multiHead ops layer seq =
    let open TransformerOps ops in
    let hs = heads layer
        outs = map (λ h → headAttention ops h seq) hs
    in map (oProj layer) (mergeHeadsSeq outs)

  block : ∀ (ops : TransformerOps)
        → TransformerOps.LayerParam ops
        → List (TransformerOps.Vec ops)
        → List (TransformerOps.Vec ops)
  block ops layer seq =
    let open TransformerOps ops in
    let att = multiHead ops layer seq
        seq1 = map (lnAttn layer) (zipWith addV seq att)
        ffnOut = map (ffn layer) seq1
    in map (lnFfn layer) (zipWith addV seq1 ffnOut)

  applyLayers : ∀ (ops : TransformerOps)
              → List (TransformerOps.LayerParam ops)
              → List (TransformerOps.Vec ops)
              → List (TransformerOps.Vec ops)
  applyLayers ops [] seq = seq
  applyLayers ops (l ∷ ls) seq = applyLayers ops ls (block ops l seq)

  forwardOps : ∀ (ops : TransformerOps)
             → TransformerOps.Param ops
             → List (TransformerOps.Token ops)
             → List (TransformerOps.Token ops)
  forwardOps ops p toks =
    let open TransformerOps ops in
    let seq0 = withPos ops p toks
        seqN = applyLayers ops (layers p) seq0
    in map (readout p) seqN

