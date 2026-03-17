{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.MetamathSurface where

import LogOS.Apps.ZFC.Metamath.SetMM.Sig as SigSurface
import LogOS.Apps.ZFC.Metamath.SetMM.Vars as VarsSurface
import LogOS.Apps.ZFC.Metamath.SetMM.Syntax as SyntaxSurface
import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Wff as ParseSurface
import LogOS.Apps.ZFC.Metamath.SetMM.Reify.WffReify as WffReifySurface
import LogOS.Apps.ZFC.Metamath.SetMM.Reify.Provable as ProvableSurface
import LogOS.Apps.ZFC.Metamath.Interpretation as InterpretationSurface
import LogOS.Apps.ZFC.Metamath.BiDirectional as BiDirectionalSurface

open SigSurface public using (Sig)
open VarsSurface public using (Vars; varsFromHyps; setVars)
open SyntaxSurface public using (PFormula; toFormula)
open ParseSurface public using (parseWff; parse⊢; parseWffBulk; parse⊢Bulk)
open WffReifySurface public using (reifyWff)
open ProvableSurface public using (reify⊢)
open InterpretationSurface public using
  ( ConclPipeline
  ; parseClosedConcl
  ; ConclPipelineWithRest
  ; parseClosedConclWithEnvBulk
  ; dropVacuousQuantifiers
  ; interpretMetaFree
  ; SetMMZFLedger
  )
open BiDirectionalSurface public using
  ( SupportFrame
  ; FormulaEntry
  ; TokenEntry
  ; toTokenEntryWithFrame
  ; toTokenEntry
  ; buildEntriesWithFrames
  ; interpretTokenEntry
  ; buildEntries
  ; mkTokenDB
  ; mkClosedFormulaEntry
  ; mkClosedTokenDB
  )
