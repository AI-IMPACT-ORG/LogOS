{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.All where

-- Index module for the ZFC domain (discoverability only).

import LogOS.ZFC.MembershipGraphSemantics as MembershipGraphSemanticsₜ
import LogOS.ZFC.WFGraph.All as WFGraphₜ
import LogOS.ZFC.SetTheory.All as SetTheoryₜ
import LogOS.ZFC.SetU.All as SetUₜ
import LogOS.ZFC.Supplementary.HF.HFFragment as HFFragmentₜ
import LogOS.ZFC.Supplementary.HF.HFGraph as HFGraphₜ

module MembershipGraphSemantics = MembershipGraphSemanticsₜ
module WFGraph = WFGraphₜ
module SetTheory = SetTheoryₜ
module SetU = SetUₜ

module Supplementary where
  module HF where
    module HFFragment = HFFragmentₜ
    module HFGraph = HFGraphₜ
