{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore where

-- ZF as a *stack of logical transformers* sharing a single boundary.
--
-- - boundary constraints are sets-as-predicates (refinement = entailment),
-- - each ZF constructor/schema is a `View` into that boundary,
-- - composition of constructors is literal `View` composition (`_∘View_`),
-- - kernels are a derived presentation: `Kernel` = boundary + code + decode.

import LogOS.Apps.ZFC.Stack.ZFCore.Context as Context
import LogOS.Apps.ZFC.Stack.ZFCore.Signature as Signature
import LogOS.Apps.ZFC.Stack.ZFCore.Laws as Laws
import LogOS.Apps.ZFC.Stack.ZFCore.Pointwise as Pointwise
import LogOS.Apps.ZFC.Stack.ZFCore.Stack as StackDef
import LogOS.Apps.ZFC.Stack.ZFCore.NoOmega as NoOmega

open Context public
open Signature public
open Laws public
open Pointwise public
open StackDef public
open NoOmega public
