{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM where

-- Implementation assembly for the Set.MM-facing adapter stack.
--
-- Use `LogOS.Apps.ZFC.MetamathSurface` for the curated public deck.
-- This file keeps the underlying parser/reifier components together but no
-- longer acts as a second flattened public-open surface.
--
-- Design stance (transformer-aligned):
-- - keep the “host ingestion port” (runtime/static Metamath DB) separate;
-- - keep the pure parsing/pretty roundtrip layers explicit;
-- - let `MetamathSurface` decide which parts belong on the public surface.

import LogOS.Apps.ZFC.Metamath.SetMM.Sig as Sig
import LogOS.Apps.ZFC.Metamath.SetMM.Syntax as Syntax
import LogOS.Apps.ZFC.Metamath.SetMM.Vars as Vars
import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Support as ParseSupport
import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Term as ParseTerm
import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Wff as ParseWff
import LogOS.Apps.ZFC.Metamath.SetMM.Reify.TermReify as ReifyTerm
import LogOS.Apps.ZFC.Metamath.SetMM.Reify.WffReify as ReifyWff
import LogOS.Apps.ZFC.Metamath.SetMM.Reify.Provable as ReifyProvable
