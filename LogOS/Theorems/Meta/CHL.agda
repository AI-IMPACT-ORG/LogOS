{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL where

-- Umbrella module for the Curry-Howard-Lambek capstone view.
-- Use the submodules to avoid name clashes (each view exposes a `For` module).

import LogOS.Theorems.Meta.CHL.Core as Coreₜ
import LogOS.Theorems.Meta.CHL.Guarded as Guardedₜ
import LogOS.Theorems.Meta.CHL.Indexed as Indexedₜ
import LogOS.Theorems.Meta.CHL.Graded as Gradedₜ
import LogOS.Theorems.Meta.CHL.2Cat as Cat2ₜ
import LogOS.Theorems.Meta.CHL.Interoperability as Interopₜ
import LogOS.Theorems.Meta.CHL.ProofTheory as Proofₜ
import LogOS.Theorems.Meta.CHL.ModelTheory as Modelₜ
import LogOS.Theorems.Meta.CHL.Category as Categoryₜ
import LogOS.Theorems.Meta.CHL.SyntaxCompleteness as Syntaxₜ
import LogOS.Theorems.Meta.CHL.Completeness as Completenessₜ
import LogOS.Theorems.Meta.CHL.Capstone as Capstoneₜ
import LogOS.Theorems.Meta.CHL.AdequacyInstances as AdequacyInstancesₜ
import LogOS.Theorems.Meta.CHL.Definition as Definitionₜ
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheoremsₜ

module Core = Coreₜ
module Guarded = Guardedₜ
module Indexed = Indexedₜ
module Graded = Gradedₜ
module Cat2 = Cat2ₜ
module Interoperability = Interopₜ
module ProofTheory = Proofₜ
module ModelTheory = Modelₜ
module Category = Categoryₜ
module SyntaxCompleteness = Syntaxₜ
module Completeness = Completenessₜ
module Capstone = Capstoneₜ
module AdequacyInstances = AdequacyInstancesₜ
module Definition = Definitionₜ
module ViewTheorems = ViewTheoremsₜ
