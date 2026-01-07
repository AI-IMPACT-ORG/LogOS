{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Lab.All where

-- Unified lab surface for agents: socket + learning + physics + networks + frameworks.

open import LogOS.API.Minimal public

module Lab where
  open import LogOS.Packs.Agents.Lab.Core public

module MetaLanguage where
  open import LogOS.Packs.Agents.MetaLanguage public

module Socket where
  open import LogOS.Packs.Agents.Socket.Ports public
  open import LogOS.Packs.Agents.Socket.Contracts public
  open import LogOS.Packs.Agents.Socket.Core public
  module FromKernelSocket where
    open import LogOS.Packs.Agents.Socket.FromKernel public
  module FromGradedKernelSocket where
    open import LogOS.Packs.Agents.Socket.FromGradedKernel public

module Learning where
  module Core where
    open import LogOS.Packs.Agents.Learning.Core public
  module FixedPoint where
    open import LogOS.Packs.Agents.Learning.FixedPoint public
  module SoftPolicy where
    open import LogOS.Packs.Agents.Learning.SoftPolicy public
  module RGFlow where
    open import LogOS.Packs.Agents.Learning.RGFlow public

module Physics where
  open import LogOS.Packs.Agents.Physics.All public

module Safety where
  module Meaningfulness where
    open import LogOS.Packs.Agents.Safety.Meaningfulness public
  module Monitor where
    open import LogOS.Packs.Agents.Safety.Monitor public
  module Audit where
    open import LogOS.Packs.Agents.Safety.Audit public
  module NoTotalAuditor where
    open import LogOS.Packs.Agents.Safety.NoTotalAuditor public

module Frameworks where
  open import LogOS.Packs.Agents.Frameworks.Core public
  open import LogOS.Packs.Agents.Frameworks.GodelMachine public
  open import LogOS.Packs.Agents.Frameworks.AIXI_Bounded public
  open import LogOS.Packs.Agents.Frameworks.OOPS public
  open import LogOS.Packs.Agents.Frameworks.MetaReasoning public
  open import LogOS.Packs.Agents.Frameworks.UniversalIR public
  open import LogOS.Packs.Agents.Frameworks.PATask public
  open import LogOS.Packs.Agents.Frameworks.PATaskAgreement public
  open import LogOS.Packs.Agents.Frameworks.KernelNative public

module Networks where
  module Core where
    open import LogOS.Packs.Agents.Networks.Core public
  module HeteroWiring where
    open import LogOS.Packs.Agents.Networks.Hetero public
  module NetworkAgent where
    open import LogOS.Packs.Agents.Networks.NetworkAgent public
  module Interop where
    open import LogOS.Packs.Agents.Networks.Interop public
  module MonitorInterop where
    open import LogOS.Packs.Agents.Networks.MonitorInterop public
  module Roles where
    open import LogOS.Packs.Agents.Networks.Roles public
  module Tensor where
    open import LogOS.Packs.Agents.Networks.Tensor public
  module NetworkSafety where
    open import LogOS.Packs.Agents.Networks.Safety public

module Comparisons where
  open import LogOS.Packs.Agents.Comparisons.Refinement public
  open import LogOS.Packs.Agents.Comparisons.Cost public
  open import LogOS.Packs.Agents.Comparisons.Limitations public

module Arguments where
  module ScalingLaws where
    open import LogOS.Packs.Agents.Arguments.ScalingLaws public
  module TransformerScaling where
    open import LogOS.Packs.Agents.Arguments.TransformerScaling public
  module TransformerFormalization where
    open import LogOS.Packs.Agents.Arguments.TransformerFormalization public
  module TransformerBridge where
    open import LogOS.Packs.Agents.Arguments.TransformerBridge public
  module TransformerScalingPipeline where
    open import LogOS.Packs.Agents.Arguments.TransformerScalingPipeline public
  module Transformer where
    open import LogOS.Packs.Agents.Arguments.Transformer public
  module LogOSDiscoveryScaling where
    open import LogOS.Packs.Agents.Arguments.LogOSDiscoveryScaling public
  module KolmogorovDiscoveryScaling where
    open import LogOS.Packs.Agents.Arguments.KolmogorovDiscoveryScaling public
  module KolmogorovOptimality where
    open import LogOS.Packs.Agents.Arguments.KolmogorovOptimality public
  module SolomonoffLearning where
    open import LogOS.Packs.Agents.Arguments.SolomonoffLearning public
  module TransformerKolmogorovScaling where
    open import LogOS.Packs.Agents.Arguments.TransformerKolmogorovScaling public

module Capstone where
  open import LogOS.Packs.Agents.Capstone public

module Examples where
  module HelloSocket where
    open import LogOS.Packs.Agents.Examples.HelloSocket public
  module HelloNetwork where
    open import LogOS.Packs.Agents.Examples.HelloNetwork public
  module ReindexedNetwork where
    open import LogOS.Packs.Agents.Examples.ReindexedNetwork public
  module NeuralSymbolicBlend where
    open import LogOS.Packs.Agents.Examples.NeuralSymbolicBlend public
